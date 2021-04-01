function expand_function_def(e)
    isjust_arglist(ex) = ex isa Expr && (ex.head in (:tuple, :block, :...) || (ex.head === :where && isjust_arglist(ex.args[1])))

    name = e.args[1]
    if isjust_arglist(name)
        expand_forms(Expr(:->, e.args...))
    else
        expand_function_def_(e)
    end
end

function expand_function_def_(e)
    name = e.args[1]
    where = if name isa Expr && name.head === :where 
        w = flatten_where_expr(name)
        if !(w.args[1] isa Expr && w.args[1].head in (:call, :(::)))
            error("invalid assignment location $(deparse(name))")
        end
        name = w.args[1]
        w.args[2:end]
    else
        # can be empty array?
        false
    end
    dcl = name isa Expr && name.head === :(::)
    rett = dcl ? decl_type(name) : core(:Any)
    name = dcl ? decl_var(name) : name

    if length(e.args) == 1 && (issymbol(name) || isglobalref(name))
        !isvalid_name(name) && error("invalid function name $(name)")
        Expr(:method, name)
    elseif !(name isa Expr)
        e
    elseif name.head === :call
        raw_typevars = where == false ? [] : where
        sparams = map(analyze_typevar, raw_typevars)
        argl = name.args
        # strip nospecialize
        annotations = map(a -> meta(a.args[1], arg_name(a.args[2])), filter(isnospecialize_meta, argl))
        body = insert_after_meta(e.args[2], annotations)
        argl = map(a -> isnospecialize_meta(a) ? a.args[2] : a, argl)
        # handle destructuring
        argl_stmts = lower_destructuring_args(argl)
        argl = argl_stmts[1]
        name = check_dotop(argl[1])
        adj_decl = function (n)
            if isdecl(n) && length(n.args) == 1
                Expr(:(::), :var"#self#", n.args[1])
            else
                n
            end
        end
        farg = isdecl(name) ? adj_decl(name) : Expr(:(::), :var"#self#", call(core(:Typeof), name))
        body = insert_after_meta(body, argl_stmts[2])
        argl = argl[2:end]
        argl = fix_arglist(arglist_unshift(argl, farg), !(any(iskwarg, argl)) && !(length(argl) > 0 && argl[1] isa Expr && argl[1].head === :parameters))
        name = if isdecl(name) || (name isa Expr && name.head in (:curly, :where))
            false
        else
            name
        end
        expand_forms(method_def_expr(name, sparams, argl, body, rett))
    else
        error("invalid assignment location $(deparse(name))")
    end
end


function method_def_expr(name, sparams, argl::Vector, body, rett)
    argl = throw_unassigned_kw_args(remove_empty_parameters(argl))
    if has_parameters(argl)
        check_kw_args(argl[1].args)
        keywords_method_def_expr(name, sparams, argl, body, rett)
    else
        method_def_expr_(name, sparams, argl, body, rett)        
    end
end

function method_def_expr_(name, sparams, argl::Vector, body, rett = Expr(:core, :Any))
    if any(iskwarg, argl)
        seen = false
        for l in argl 
            if iskwarg(l)
                seen = true
            elseif seen && !isvararg(l)
                error("optional positional argumetns must occur at end")
            end
        end
        kws, argl = separate(iskwarg, argl)
        opt, dfl = [], []
        for kw in kws
            push!(opt, kw.args[1])
            push!(dfl, kw.args[2])
        end
        vararg, req = separate(isvararg, argl)
        optional_positional_defs(name, sparams, req, opt, dfl, body, [req;opt;vararg], rett)
    else
        names = map(x->x[1], sparams) # need to check format of sparams
        anames = map(x -> isunderscore_symbol(x) ? UNUSED : x, llist_vars(argl))
        unused_names = filter(x -> x != UNUSED, anames)
        ename = isnodot_sym_ref(name) ? name : :nothing

        if has_dups(unused_names)
            error("function argument name not unique")
        end
        if has_dups(names)
            error("function static parameter names not unique")
        end
        if any(x -> x != UNUSED && x in names, anames)
            error("function argument and static parameter names must be distinct")
        end
        if name isa Symbol && !issym_ref(name) && !isvalid_name(name)
            error("invalid function name $(deparse(name))")
        end
        loc = maybe_remove_functionloc!(body)
        generator = if expr_contains_p(isif_generated, body, !isfunction_def)
            gen = generated_version(body)
            nongen = non_generated_version(body)
            gname = Symbol(gensy(), "#", current_julia_module_counter())
            gf = make_generator_function(gname, names, anames, gen)
            body = insert_after_meta(nongen, [Expr(:meta, :generated, 
                Expr(:new, 
                    Expr(:core, :GeneratedFunctionStub),
                    gname,
                    Expr(:list, anames),
                    isempty(sparams) ? :nothing : map(x->x[1], sparams), # sparams structure?
                    loc.args[1], #lno structure?
                    Expr(:inert, loc.args[2]),
                    false
                    ))])
            [gf]
        else
            []
        end
        types = llist_types(argl)
        body = method_lambda_expr(argl, body, rett)
        temps = map(x -> make_ssavalue(), names)
        renames = Dict(names[i] => temps[i] for i in 1:length(names))
        mdef = if isempty(sparams)
            Expr(:method, ename, 
                call(core(:svec), 
                    call(core(:svec), dots_to_vararg(types)...),
                    call(core(:svec)),
                    inert(loc)),
                body)
        else
            sp = map(bounds_to_TypeVar, sparams)
            assigns = []
            ren = Dict()
            for i = 1:length(names)
                assign = make_assignment(temps[i], replace_vars(sp[i], ren))
                ren[names[i]] = temps[i]
                push!(assigns, assign)
            end
            Expr(:method, ename,
                Expr(:block,
                    assigns...,
                    call(core(:svec), call(Expr(:core, :svec),
                                dots_to_vararg(map(ty -> replace_vars(ty, renames), types))...),
                        call(core(:svec), temps...),
                        Expr(:inert, loc))),
                body)
        end
        if issymbol(name) || isglobalref(name)
            block(generator..., Expr(:method, name), mdef, Expr(:unnecessary, name))
        elseif !isempty(generator)
            block(generator..., mdef)
        else
            mdef
        end
    end
end



function fix_arglist(l, unused = true)
    if anybutlast(isvararg, l)
        error("invalid \"...\" on non-final argument")
    else
        map(l) do a
            if ispair(a) && a.head == :kw
                Expr(:kw, fill_missing_argname(a.args[1], unused), a.args[2])
            elseif ispair(a) && a.head === :...
                Expr(:..., fill_missing_argname(a.args[1], unused))
            else
                fill_missing_argname(a, unused)
            end
        end
    end
end


function lower_destructuring_args(argl)
    function check_lhs(a)
        if expr_contains_p(e -> isdecl(e) || isassignment(e) || iskwarg(e), a)
            error("invalid argument destructuring syntax $(deparse(a))")
        else
            a
        end
    end
    function transform_arg(a)
        if a isa Expr && a.head == :tuple
            a2 = gensy()
            (a2, Expr(:local, Expr(:(=), check_lhs(a), a2)))
        elseif (isdecl(a) && length(a.args) == 2) || iskwarg(a)
            x = transform_arg(a.args[1])
            (Expr(a.head, x[1], a.args[2]), x[2])
        elseif isvararg(a)
            x = transform_arg(a.args[1])
            (Expr(:..., x[1]), x[2])
        else
            (a, false)
        end
    end
    newa, stmts = [], []
    for a in argl
        a = transform_arg(a)
        push!(newa, a[1])
        if a[2] !== false
            push!(stmts, a[2])
        end
    end
    newa, isempty(stmts) ? stmts : [nothing]
end


function method_lambda_expr(argl::Vector, body::Expr, rett)
    argl = map(function (x)
        n = arg_name(x)
        if isunderscore_symbol(n)
            UNUSED
        else
            n
        end
    end, argl)
    body = blockify(body)
    
    Expr(:lambda, argl, [], scope_block(if rett == Expr(:core, :Any)
            body
        else
            meta = take_while(x -> ispair(x) && x.head in (:line, :meta), body.args)
            R = make_ssavalue()
            Expr(body.head, 
                meta...,
                Expr(:(=), R, rett),
                Expr(:meta, Symbol("ret-type"), R),
                body.args[length(meta) + 1:end]...
            )
    end))
end


function keywords_method_def_expr(name, sparams, argl, body, rett)
    kargl = argl[1].args
    annotations = map(a -> meta(a.args[1], arg_name(a.args[1].args[1])), filter(isnospecialize_meta, kargl)) #todo
    kargl = map(a -> isnospecialize_meta(a) ? a.args[2] : a, kargl)
    pargl = argl[2:end]
    body = blockify(body)
    ftype = decl_type(pargl[1])
    vararg =  let l = isempty(pargl) ? [] : last(pargl)
        if isvararg(l) || isvarargexpr(l)
            [l]
        else
            []
        end
    end
    pargl_all = pargl
    pargl = isempty(vararg) ? pargl : pargl[1:end-1]
    not_optional = map(a -> iskwarg(a) ? a.args[1] : a, pargl)
    restkw = isvararg(last(kargl)) ? [last(kargl).args[1]] : []
    kargl = let kws = isempty(restkw) ? kargl : kargl[1:end-1]
        if any(isvararg, kws)
            error("invalid ... on non-final keyword agument")
        else
            kws
        end
    end
    vars = map(x -> x.args[1], kargl)
    vals = map(x -> x.args[2], kargl)
    keynames = map(decl_var, vars)
    ordered_defaults = any(v -> contains(x -> x == v, vals), keynames)
    prologue = extract_method_prologue(body)
    stmts = body.args
    positional_sparams = filter_sparams([pargl_all], sparams)
    keyword_sparams = filter(s -> !any(p -> p.head == s.head), positional_sparams)
    
    kw = gensy()
    rkw = isempty(restkw) ? make_ssavalue() : Symbol(restkw[1], "...")
    mangled = let und = name !== nothing && undot_name(name)
        Symbol(name !== nothing && first(string(name)) == '#' ? "" : "#", und == false ? :_ : und, "#", current_julia_module_counter())
    end

    methname = (issymbol(name) || isglobalref(name) ? Expr(:method, name) : ())
    # call with keyword args pre-sorted - original method code goes here
    methdef1 = method_def_expr_(mangled, 
                        sparams, 
                        [Expr(:(::), mangled, call(core(:typeof)), mangled), vars..., restkw..., not_optional..., vararg...],
                        insert_after_meta(Expr(:block, stmts...), [meta(:nkw, length(vars) + length(restkw)), annotations...]), 
                        rett)
    # call with no keyword args
    methdef2 = method_def_expr_(
                        name, 
                        positional_sparams, 
                        pargl_all, 
                        Expr(:block, 
                            without_generated(prologue)...,
                            (let ret = Expr(:return, call(mangled, (ordered_defaults ? keynames : vals)...,
                                (isempty(restkw) ? () : [call(top(:pairs), (call(core(:NamedTuple))))])...,
                                map(arg_name, pargl)...,
                                (isempty(vararg) ? () : [(Expr(:..., arg_name(first(vararg))))])...))
                                if ordered_defaults
                                    scopenest(keynames, vals, ret)
                                else
                                    ret
                                end
                            end)))
    # call with unsorted keyword args. this sorts and re-dispatches
    
    methdef3 = method_def_expr_(name, 
                positional_sparams, 
                [Expr(:(::), any(iskwarg, pargl) ? gensy() : UNUSED, call(core(:kwftype)), ftype), kw, pargl..., vararg...], 
                Expr(:block,
                    filter(islinenum, prologue)...,
                    map(m -> meta(m.args[1], filter(v -> !(v in keynames), m.args[2:end])), filter(isnospecialize_meta, prologue))...,
                    scopenest(keynames, map((v, dflt) -> let 
                        k = decl_var(v)
                        rval0 = call(top(:getindex), kw, inert(k))
                        rval = if isdecl(v) && !(any(s -> expr_contains_eq(s.head, v.args[2]),keyword_sparams))
                            T = v.args[2]
                            temp = make_ssavalue()
                            Expr(:block, make_assignment(temp, rval0),
                                Expr(:if, call(core(:isa), temp, T), nothing, call(core(:throw), Expr(:new, core(:TypeError), inert(:var"keyword argument"), inert(k), T, temp))), temp)
                        else
                            rval0
                        end
                        Expr(:if, call(top(:haskey), kw, Expr(:quote, k)), rval, dflt)
                    end, vars, vals),
                    Expr(:block,
                        Expr(:(=), rkw, call(top(:pairs), isempty(keynames) ? kw : call(top(:structdiff), kw, Expr(:curly, core(:NamedTuple), Expr(:tuple, map(quotify, keynames)...))))),
                        (isempty(restkw) ? [Expr(:if, call(top(:isempty), rkw), nothing, call(top(:kwerr), kw, map(arg_name, pargl)..., (isempty(vararg) ? () : [Expr(:..., arg_name(vararg[1]))])...))] : [])...,
                        Expr(:return, call(mangled, 
                                        keynames..., 
                                        (isempty(restkw) ? () : [rkw])...,
                                        map(arg_name, pargl)...,
                                        (isempty(vararg) ? () : [Expr(:..., arg_name(first(vararg)))])...))))))
    
    Expr(:call, core(:ifelse), false, false, block(
        methname,
        methdef1,
        methdef2,
        methdef3,
        !issymbol(name) ? nothing : name
    ))
end

function extract_method_prologue(body)
    if ispair(body)
        take_while(e -> ispair(e) && (e.head == :line || e.head == :meta), body.args)
    else
        []
    end
end

function make_generator_function(name, sp_names, arg_names, body)
    arg_names = vcat(sp_names, map(n -> n == :var"#sefl#" ? gensy() : n, arg_names)...)
    body = insert_after_meta(body, Expr(:meta, :nospecialize, arg_names...))
    Expr(:block, Expr(:global, name), Expr(:function, call(name, arg_names...), body))
end


function generated_part_(x, genpart)
    if isatom(x) || isquoted(x) || isfunction_def(x)
        x
    elseif isif_generated(x)
        if genpart
            Expr(:$, x.args[2])
        else
            x.args[3]
        end
    else
        Expr(x.head, map(e -> generated_part_(e, genpart), x.args)...)
    end
end

function without_generated(stmts)
    filter(x -> !(isgenerated_meta(x) || isgenerated_only_meta(x)), stmts)
end

function generated_version(body)
    Expr(:block, julia_bq_macro(generated_part_(body, true)))
end

function non_generated_version(body)
    generated_part_(body, false)
end

function filter_sparams(expr, sparams)
    filtered = []
    for (i,p) in enumerate(sparams)
        if expr_contains_eq(p[1], expr) ||
            any(v -> expr_contains_eq(p[1], v), sparams[i+1:end]) # todo : optimize
            push!(filtered, p)
        end
    end
    filtered
end

function optional_positional_defs(name, sparams, req, opt, dfl, body, overall_argl, rett)
    prologue = without_generated(extract_method_prologue(body))
    Expr(:block,
        map(function (n)
            passed = [req; opt[1:n-1]]
            sp = filter_sparams(Expr(:list, passed), sparams)
            vals = list_tail(dfl, n)
            absent = list_tail(opt, n)
            body1 = if any(defaultv -> contains(e -> any(a -> contains(u -> u == e, a), absent), defaultv), vals)
                Expr(:block, prologue..., call(arg_name(first(req)), map(arg_name, passed[2:end])..., vals[1]))
            else
                Expr(:block, prologue..., call(arg_name(first(req)), map(arg_name, passed[2:end])..., vals...))
            end
            method_def_expr_(name, sp, passed, body1)
        end,
        1:length(opt))...,
        method_def_expr_(name, sparams, overall_argl, body, rett)
    )
end

function remove_empty_parameters(argl)
    if has_parameters(argl) && isempty(argl[1].args)
        argl[2:end]
    else
        argl
    end
end

function check_kw_args(kw)
    invalid = filter(x -> !(iskwarg(x) || isvararg(x) || (isnospecialize_meta(x) && (iskwarg(x.args[2]) || isvararg(x.args[2])))), kw)

    if !isempty(invalid)
        if first(invalid) isa Expr && first(invalid).head == :parameters
            error("more than one semicolon in argument list")
        else
            error("invalid keyword argument syntax")
        end
    end
end

function throw_unassigned_kw_args(argl)
    throw_unassigned(argname) = call(Expr(:core, :throw), call(Expr(:core, :UndefKeywordError), inert(argname)))
    function to_kw(x)
        if issymbol(x)
            Expr(:kw, x, throw_unassigned(x))
        elseif isdecl(x)
            Expr(:kw, x, throw_unassigned(x.args[1]))
        elseif isnospecialize_meta(x)
            Expr(:meta, x.args[1], to_kw(x.args[2]))
        else
            x
        end
    end
    if has_parameters(argl)
        # just replace argl[1] ?
        [Expr(:parameters, map(to_kw, argl[1].args)...); argl[2:end]]
    else
        argl
    end
end

function arglist_unshift(sig::Vector, item)
    if has_parameters(sig)
        insert!(sig, 2, item)
    else
        pushfirst!(sig, item)
    end
    sig
end

function maybe_remove_functionloc!(body)
    prologue = extract_method_prologue(body)
    prologue_lnos = filter(islinenum, prologue)
    functionloc = !isempty(prologue_lnos) ? first(prologue_lnos) : let lnos = filter(islinenum, body.args); isempty(lnos) ? LineNumberNode(0, "") : first(lnos) end
    if  length(prologue_lnos) > 1
        for (i, stmt) in enumerate(body.args) 
            if functionloc == stmt
                deleteat!(body.args, i)
                return functionloc
            end
        end
    end
    return functionloc
end
