splat_token = :__splat__

function bq_expand_arglist(lst, d)
    out = []
    for nxt in lst
        nxt = julia_bq_expand_(nxt, d)
        if nxt isa Expr && nxt.head === splat_token
            pushfirst!(out, nxt)
        else
            push!(out, nxt)
        end
    end
    out
end

function julia_bq_expand_(x, d)
    if issymbol(x) || isssavalue(x)
        Expr(:inert, x)
    elseif isatom(x) || (x isa Expr && x.head in (_true, _false)) || x isa Bool
        x
    elseif d == 0 && x.head == :$
        if length(x.args) == 1
            if isvararg(x.args[1])
                Expr(:..., x.args[1].args[1])
            else
                x.args[1]
            end
        else
            Expr(splat_token, x.args...)
        end
    elseif !contains(e -> e isa Expr && e.head === :$, x)
        if x.head === :line
            inert(x)
        else
            Expr(:copyast, inert(x))
        end
    else
        if x.head === :inert
            call(core(:QuoteNode), bq_expand_arglist(x.args, d)...)
        elseif x.head === :line
            call(core(:LineNumberNode), bq_expand_arglist(x.args, d)...)
        elseif x.head === :quote
            call(core(:_expr), bq_expand_arglist(x, d + 1)...)
        elseif x.head === :$
            call(core(:_expr), bq_expand_arglist(x, d - 1)...)
        else
            call(core(:_expr), bq_expand_arglist(x, d)...)
        end
    end
end

function julia_bq_expand(x, d)
    e = julia_bq_expand_(x, d)
    if e isa Expr && e.head === splat_token
        Expr(:error, "\"...\" expression outside call")
    else
        e
    end
end

function vars_introduced_by_patterns(x)
    if (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :call) && isexpr(x.args[1].args[1], :curly)
        # name = x.args[1].args[1].args[1]
        sparams = x.args[1].args[1].args[2:end]
        argl = x.args[1].args[2:end]
        # body = x.args[2]
        Expr(:varlist, safe_llist_positional_args(fix_arglist(argl))..., typevar_names(sparams)...)
    elseif (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :call)
        name = x.args[1].args[1]
        argl = x.args[1].args[2:end]
        Expr(:varlist, [safe_llist_positional_args(fix_arglist([self_argname(name); argl]))])
    elseif (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :(::)) && isexpr(x.args[1].args[1], :call)
        name = x.args[1].args[1].args[1]
        argl = x.args[1].args[1].args[2:end]
        Expr(:varlist, [safe_llist_positional_args(fix_arglist([self_argname(name); argl]))])
    elseif (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :where)
        wheres = x.args[1].args[2:end]
        others = vars_introduced_by_patterns(x.args[1].args[1])
        Expr(:varlist, [isexpr(others, :varlist) ? [] : others.args; typevar_names(wheres)])
    elseif isexpr(x, :function) && isexpr(x.args[1], :tuple)
        vars_introduced_by_patterns(Expr(:(->), Expr(:tuple, x.args[1].args...), x.args[2]))
    elseif isexpr(x, :(->))
        a = isexpr(x.args[1], :tuple) ? a.args : [a]
        Expr(:varlist, safe_llist_positional_args(fix_arglist(a)))
    elseif isexpr(x, :where)
        Expr(:varlist, typevar_names(x.args[2:end])...)
    elseif isexpr(x, :(=)) && isexpr(x.args[1], :curly)
        Expr(:varlist, typevar_names(x.args[1].args[2:end])...)
    elseif isexpr(x, :let)
        binds = let_binds(x)
        vars = []
        for bind in binds
            if issymbol(bind) || isdecl(bind)
                push!(vars, decl_var(bind))
            elseif isexpr(bind, :(=)) && length(bind.args) == 2
                if issymbol(bind.args[1]) || isdecl(bind.args[1])
                    push!(vars, decl_var(bind.args[1]))
                elseif eventually_call(bind.args[1])
                    asgn = julia_expand0(bind, "none", 0).args[1]
                    push!(vars, asgn.args[1])
                elseif isexpr(bind.args[1], :tuple)
                    append!(vars, decl_var.(lhs_vars(bind.args[1])))
                else
                    nothing
                end
            else
                return nothing
            end
        end
        Expr(:varlist, vars...)
    elseif isexpr(x, :macro)
        vars_introduced_by_patterns(Expr(:->, Expr(:tuple, x.args[1].args[2:end]), x.args[2]))
    elseif isexpr(x, :try) && length(x.args) == 4 || length(x.args) == 3
        !isexpr(x.args[2], _false) ? Expr(:varlist, x.args[2]) : nothing
    elseif isexpr(x, :struct)
        tn = typedef_expr_name(x.args[2])
        tv = typedef_expr_tvars(x.args[2])
        Expr(:varlist, (unescape(tn), unescape(tn)), (:new, :new), typevar_names(tv))
    elseif isexpr(x, :abstract)
        tn = typedef_expr_name(x.args[1])
        tv = typedef_expr_tvars(x.args[1])
        Expr(:varlist, (unescape(tn), unescape(tn)), typevar_names(tv))
    elseif isexpr(x, :primitive)
        tn = typedef_expr_name(x.args[1])
        tv = typedef_expr_tvars(x.args[1])
        Expr(:varlist, (unescape(tn), unescape(tn)), (:new, :new), typevar_names(tv))
    end
end

function keywords_introduced_by_patterns(x)
    if (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :call) && isexpr(x.args[1].args[1], :curly)
        argl = x.args[1].args[2:end]
        Expr(:varlist, safe_llist_positional_args(fix_arglist(argl))...)
    elseif (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :call)
        argl = x.args[1].args[2:end]
        Expr(:varlist, safe_llist_positional_args(fix_arglist(argl))...)
    elseif (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :(::)) && isexpr(x.args[1].args[1], :call)
        argl = x.args[1].args[1].args[2:end]
        Expr(:varlist, safe_llist_positional_args(fix_arglist(argl))...)
    elseif (isexpr(x, :function) || isexpr(x, :(=))) && isexpr(x.args[1], :where)
        keywords_introduced_by_patterns(Expr(:function, x.args[1].args[1], x.args[2]))
    end
end

pair_with_gensyms(v) = map(s -> s isa Expr ? s : (s, named_gensy(s)), v)

unescape(e) = isexpr(e, :escape) ? e.args[1] : e


function typedef_expr_name(e)
    if isatom(e)
        e
    elseif e.head in (:curly, :<:)
        typedef_expr_name(e.args[1])
    else
        e
    end
end

function typedef_expr_tvars(e)
    if isatom(e)
        []
    elseif e.head === :<:
        typedef_expr_tvars(e.args[1])
    elseif e.head === :curly
        e.args[2:end]
    else
        []
    end
end

typevar_expr_name(e) = first(analyze_typevar(e))

typevar_names(lst) = map(v -> try typevar_expr_name(v) catch; [] end, lst)

function try_arg_name(v)
    if issymbol(v) 
        [v]
    elseif isatom(v)
        []
    else
        if v.head in (:..., :kw, :(::), :(=))
            try_arg_name(v.args[1])
        elseif v.head === :escape
            [v]
        elseif v.head === :var"hygienic-scope"
            try_arg_name(v.args[1])
        elseif v.head === :meta
            isnospecialize_meta(v, true) ? try_arg_name(v.args[2]) : []
        else 
            []
        end
    end
end

function safe_arg_names(lst, escaped = false)
    map(function (v)
        vv = try_arg_name(v)
        if escaped == !isempty(vv) && isexpr(first(vv), :escape)
            escaped ? [first(vv.args[1])] : vv
        else
            []
        end
    end, lst)
end

function safe_llist_positional_args(lst, escaped = false)
    params, normal = separate(a -> isexpr(a, :parameters), lst)
    safe_arg_names([normal; map(a -> filter(isvararg, a.args), params)], escaped)
end

function safe_llist_keyword_args(lst)
    kwargs = vcat(map(x -> x.args, filter(a -> isexpr(a, :parameters), lst))...)
    kwargs = filter(!isvararg, kwargs)
    vcat(safe_arg_names(kwargs, false), safe_arg_names(kwargs, true), safe_llist_positional_args(lst, true))
end

self_argname(name) = isexpr(name, :(::)) && length(name.args) == 2 ? [name.args[1]] : []


function resolve_in_function_lhs(e, env, m, parent_scope, inarg)
    recur(x) = resolve_in_function_lhs(x, env, m, parent_scope, inarg)
    other(x) = resolve_expansion_vars_with_new_env(x, env, m, parent_scope, inarg)

    if e.head === :where
        Expr(:where, recur(e.args[1]), other.(e.args[2:end])...)
    elseif e.head === :(::)
        Expr(:(::), recur(e.args[1]), other(e.args[2]))
    elseif e.head === :call
        Expr(:call, other(e.args[1]), map(x -> resolve_expansion_vars_with_new_env(x, env, m, parent_scope, true), e.args[2:end])...)
    elseif e.head === :tuple
        Expr(:tuple, map(x -> resolve_expansion_vars_with_new_env(x, env, m, parent_scope, true), e.args)...)
    else
        other(e)
    end
end


function tuple_wrap_arrow_sig(e)
    if isatom(e)
        Expr(:tuple, e)
    elseif e.head === :where
        Expr(:where, tuple_wrap_arrow_sig(e.args[1]), e.args[2:end]...)
    elseif e.head === :tuple
        e
    elseif e.head === :escape
        Expr(:escape, tuple_wrap_arrow_sig(e.args[1]))
    else
        Expr(:tuple, e)
    end
end

function julia_expand_macroscope(e)
    julia_expand_macroscopes_(rename_symbolic_labels(julia_expand_quotes(e)))
end

function julia_expand_macroscopes_(e)
    if !(e isa Expr) || e.head in (:inert, :module)
        e
    elseif e.head === :var"hygienic-scope"
        form = e.args[1]
        modu = e.args[2]
        resolve_expansion_vars(form, modu)
    else
        ex = Expr(e.head)
        for a in e.args
            push!(ex.args, julia_expand_macroscopes_(a))
        end
        ex
    end
end

function resolve_expansion_vars(e, m)
    resolve_expansion_vars_with_new_env(e, [], m, [], false, true)
end

function resolve_expansion_vars_with_new_env(x, env, m, parent_scope, inarg, outermost = false)
    resolve_expansion_vars_(x, x isa Expr && x.head === :let ? env : new_expansion_env_for(x, env, outermost), m, parent_scope, inarg)
end


function resolve_expansion_vars_(e, env::Dict, m, parent_scope, inarg)
    if e === :end || e === :ccall || e === :cglobal
        e
    elseif issymbol(e)
        a = get(env, e, nothing)
        if a !== nothing
            a[2]
        else
            m !== nothing ? Expr(:globalref, m, e) : e
        end
    elseif !(e isa Expr) || isquoted(e)
        e
    else
        if e.head in (:ssavalue, :macrocall, :symboliclabel, :symbolicgoto)
            e
        elseif e.head === :escape
            if isempty(parent_scope)
                julia_expand_macroscopes_(e.args[1])
            else
                scope = first(parent_scope) # or last?
                env = first(scope)
                m = scope[2]
                parent_scope = parent_scope[2:end]
                resolve_expansion_vars_with_new_env(e.args[1], env, m, parent_scope, inarg)
            end
        elseif e.head === :global
            arg = e.args[1]
            if issymbol(arg)
                e
            elseif isassignment(arg)
                Expr(:global, make_assignment(unescape(arg.args[1]), resolve_expansion_vars_with_new_env(arg.args[2], env, m, parent_scope, inarg)))
            else
                Expr(:global, resolve_expansion_vars_with_new_env(arg, env, m, parent_scope, inarg))
            end
        elseif e.head in (:using, :import, :export, :meta, :line, :inbounds, :boundscheck, :oopinfo)
            map(unescape, e)
        elseif e.head === :struct
            Expr(:struct, e.args[1], resolve_expansion_vars_(e.args[2], env, m, parent_scope, inarg), block(map(function (x)
                if isatom(x)
                    x
                elseif x isa Expr && x.head === :(::)
                    resolve_expansion_vars_(x.args[2], env, m, parent_scope, inarg)
                else parent_scope
                    resolve_expansion_vars_with_new_env(x, env, m, parent_scope, inarg)
                end
            end, e.args[3].args)))
        elseif e.head === :parameters
            ex = Expr(:parameters)
            for x in e.args
                x = !inarg && issymbol(x) ? Expr(:kw, x, x) : x
                push!(ex.args, resolve_expansion_vars_(x, env, m, parent_scope, false))
            end
            ex
        elseif e.head === :(->)
            Expr(:(->), resolve_in_function_lhs(tuple_wrap_arrow_sig(e.args[1]), env, m, parent_scope, inarg), resolve_expansion_vars_with_new_env(e.args[2], env, m, parent_scope, inarg))
        elseif e.head in (:function, :(=))
            if e.args[1] isa Expr && isfunction_def(e) && length(e.args) > 1
                Expr(e.head, resolve_in_function_lhs(e.args[1], env, m, parent_scope, inarg), resolve_expansion_vars_with_new_env(e.args[2], env, m, parent_scope, inarg))
            else
                Expr(e.head, map(x -> resolve_expansion_vars_with_new_env(x, env, m, parent_scope, inarg), e.args)...)
            end
        elseif e.head === :kw
            if !(length(e.args) > 1)
                e
            elseif e.args[1] isa Expr && e.args[1].head === :(::)
                Expr(:kw, Expr(:(::), resolve_expansion_vars_(e.args[1].args[1], env, m, parent_scope, inarg)))
                e
            elseif e.args[1] isa Expr && e.args[1].head
                e
            elseif e.args[1] isa Expr && e.args[1].head === :(::)
                Expr(:kw, Expr(:(::), inarg ? resolve_expansion_vars_(e.args[1].args[1], env, m, parent_scope, inarg) : unescape(e.args[1].args[1]), resolve_expansion_vars_(e.args[1].args[2], env, m, parent_scope, inarg)), resolve_expansion_vars_with_new_env(e.args[2], env, m, parent_scope, inarg))
            else
                Expr(:kw, inarg ? resolve_expansion_vars_(e.args[1], env, m, parent_scope, inarg) : unescape(e.args[1]), resolve_expansion_vars_with_new_env(e.args[2], env, m, parent_scope, inarg))resolve_expansion_vars_with_new_env
            end
        elseif e.head === :let
            newenv = new_expansion_env_for(e, env)
            body = resolve_expansion_vars_(e.args[2], newenv, m, parent_scope, inarg)
            binds = let_binds(e)

            Expr(:let, block(
                map(function (bind)
                    if isassignment(bind)
                        make_assignment(resolve_expansion_vars_(make_assignment(bind.args[1], 0), newenv, m, parent_scope, inarg).args[1], 
                            resolve_expansion_vars_(bind.args[2], env, m, parent_scope, inarg))
                    else
                        bind
                    end
                end, binds)
            ), body)
        elseif e.head === :var"hygienic-scope"
            parent_scope = vcat(parent_scope, [env, m])
            body = e.args[1]
            m = e.args[2]
            resolve_expansion_vars_with_new_env(body, env, m, parent_scope, inarg, true)
        elseif e.head === :tuple
            ex = Expr(e.head)
            for x in e.args
                if isassignment(x)
                    push!(ex.args, make_assignment(unescape(x.args[1]), resolve_expansion_vars_with_new_env(x.args[2], env, m, parent_scope, inarg)))
                else
                    push!(ex.args, resolve_expansion_vars_with_new_env(x, env, m, parent_scope, inarg))
                end
            end
            ex
        else
            ex = Expr(e.head)
            for x in e.args
                push!(ex.args, resolve_expansion_vars_with_new_env(x, env, m, parent_scope, inarg))
            end
            ex
        end
    end
end

function new_expansion_env_for(x, env, outermost = false)
    introduced = vars_introduced_by_patterns(x)
    if isatom(x) || (!outermost && !(introduced isa Expr && introduced.head === :varlist))
        env
    else
        globals = find_declared_vars_in_expansion(x, :global)
        vlist = isexpr(introduced, :varlist) ? introduced.args : []
        pairs, vnames = separate(isa(Expr), vlist)

        v = setdiff(unique(vcat(find_declared_vars_in_expansion(x, :local), find_assigned_vars_in_expansion(x), vnames)), globals)
        
        vcat(
            pairs,
            filter(v -> first(v) in env, pair_with_gensyms(v)),
            map(v -> (v, v), keywords_introduced_by(x)),
            env
        ) 
    end
end

function decl_varS(e)
    if isatom(e)
        e
    elseif e.head === :escape
        []
    elseif e.head in (:call, :(=), :curly, :(::), :where)
        decl_varS(e.args[1])
    else
        decl_var(e)
    end
end

function resume_on_escape(lam, e, nblocks)
    if !(e isa Expr) || isquoted(e)
        []
    else
        if e.head in (:lambda, :module, :toplevel)
            []
        elseif e.head === :var"hygienic-scope"
            resume_on_escape(lam, e.args[1], nblocks + 1)
        elseif e.head === :escape
            if nblocks == 0
                lam(e.args[1])
            else
                resume_on_escape(lam, e.args[1], nblocks - 1)
            end
        else
            foldl((a,l) -> vcat(l, resume_on_escape(lam, a, nblocks)), e.args)
        end
    end
end

function find_declared_vars_in_expansion(e, decl, outer = true)
    if !(e isa Expr) || isquoted(e)
        []
    elseif e.head === :escape
        []
    elseif e.head === :var"hygienic-scope"
        resume_on_escape(e -> find_declared_vars_in_expansion(e, decl, outer), e.args[1], 0)
    elseif e.head === :decl
        map(decl_varS, e.args)
    elseif !outer && isfunction_def(e)
        []
    else
        vcat(map(x -> find_declared_vars_in_expansion(x, decl, false), e.args)...)
    end
end

function find_assigned_vars_in_expansion(e, outer = true)
    if !(e isa Expr) || isquoted(e)
        []
    elseif e.head === :escape
        []
    elseif e.head === :var"hygienic-scope"
        resume_on_escape(e -> find_assigned_vars_in_expansion(e, outer), e.args[1], 0)
    elseif !outer && isfunction_def(e)
        fname = if e.head == :(=)
            decl_varS(e.args[1])
        elseif e.head === :function
            if isatom(e.args[1])
                e.args[1]
            elseif e.args[1].head === :tuple
                false
            else
                decl_varS(e.args[1])
            end
        else
            false
        end

        if issymbol(fname)
            [fname]
        else
            []
        end
    elseif e.head === :(=) && !isfunction_def(e)
        vcat(filter(issymbol, decl_varS(e.args[1])), find_assigned_vars_in_expansion(e.args[2], false))
    elseif e.head === :tuple
        vcat(map(x -> find_assigned_vars_in_expansion(isassignment(x) ? x.args[2] : x, false), e.args)...)
    else
        vcat(map(x -> find_assigned_vars_in_expansion(x, false), e.args)...)
    end
end

function keywords_introduced_by(e)
    v = keywords_introduced_by_patterns(e)
    isexpr(v, :varlist) ? v.args : []
end

function julia_expand_quotes(e)
    if e isa QuoteNode
        julia_expand_quotes(julia_bq_macro(e.value))
    elseif !(e isa Expr)
        e
    elseif e.head in (:inert, :module)
        e
    elseif e.head === :quote
        julia_expand_quotes(julia_bq_macro(e.args[1]))
    elseif contains(e -> isexpr(e, :quote), e.args)
        e
    else
        Expr(e.head, map(julia_expand_quotes, e.args)...)
    end
end

julia_bq_macro(x) = julia_bq_expand(x, 0)

function rename_symbolic_labels_(e, relabels, parent_scope)
    if !(e isa Expr) || isquoted(e)
        e
    elseif e.head === :var"hygienic-scope"
        parent_scope = [relabels; parent_scope]
        body = e.args[1]
        m = e.args[2]
        Expr(e.head, rename_symbolic_labels_(e.args[1], Dict(), parent_scope), m)
    elseif e.head === :escape && !isempty(parent_scope)
        Expr(e.head, rename_symbolic_labels_(e.args[1], parent_scope))
    elseif e.head in (:symbolicgoto, :symboliclabel)
        s = e.args[1]
        havelabel = (isempty(parent_scope) || !issym_dot(s)) ? s : get(relabels, s, false)
        newlabel = havelabel != false ? havelabel : named_gensy(s)
        if havelabel == false
            relabels[s] = newlabel
        else
            Expr(e.head, newlabel)
        end
    else
        Expr(e.head, map(x -> rename_symbolic_labels_(x, relabels, parent_scope), e.args)...)
    end
end

rename_symbolic_labels(e) = rename_symbolic_labels_(e, Dict(), [])