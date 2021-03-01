function expand_let(e::Expr, ishard::Bool = true)
    ex = e.args[2]
    binds = let_binds(e)
    hs = ishard ? (Expr(:hardscope),) : ()
    expand_forms(
    if isempty(binds)
        blk = scope_block(block(hs..., ex))
    else
        blk = ex
        for bind in reverse(binds)
            if issymbol(bind) || isdecl(bind)
                blk = scope_block(block(hs..., Expr(:local, (bind)), blk))
            elseif bind isa Expr && length(bind.args) == 2 && bind.head == :(=)
                if eventually_call(bind.args[1])
                    name = assigned_name(bind.args[1])
                    !issymbol(name) && error("invalid let syntax")
                    blk = scope_block(block(
                        hs...,
                        if expr_contains_eq(name, bind.args[2])
                            Expr(:local, name)
                        else
                            local_def(name)
                        end,
                        bind,
                        blk))
                elseif issymbol(bind.args[1]) || isdecl(bind.args[1])
                    vname = decl_var(bind.args[1])
                    blk = if expr_contains_eq(vname, bind.args[2])
                        scope_block(block(
                            hs...,
                            make_assignment(:tmp, bind.args[2]),
                            scope_block(block(local_def(bind.args[1]),
                            make_assignment(vname, :tmp),
                            blk))))
                    else
                        scope_block(block(
                            hs...,
                            local_def(bind.args[1]),
                            make_assignment(vname, bind.args[2]),
                            blk))
                    end
                elseif bind.args[1] isa Expr && bind.args[1].head == :tuple
                    vars = lhs_vars(bind.args[1])
                    blk = if expr_contains_p(x -> x in vars, bind.args[2])
                        temp = make_ssavalue()
                        block(
                            make_assignment(temp, bind.args[2]),
                            scope_block(block(
                                hs...,
                                map(local_def, vars)...,
                                make_assignment(bind.args[1], temp),
                                blk)))
                    else
                        scope_block(block(
                            hs...,
                            map(local_def, vars),
                            bind,
                            blk))
                    end
                end
            else 
                error("invalid let syntax")
            end
        end
        blk
    end
    )
end

function expand_macro_def(e)
    if e.args[1] isa Expr && e.args[1].head == :call && issymbol(e.args[1].args[1])
        anames = remove_empty_parameters(e.args[1].args[2:end])
        has_parameters(anames) && error("macros cannot accept keyword arguments")
        
        expand_forms(Expr(:function, 
            call(Symbol("@", e.args[1].args[1]),
                Expr(:(::), :__source__, core(:LineNumberNode)),
                Expr(:(::), :__module__, core(:Module)),
                map(v -> issymbol(v) ? meta(:nospecialize, v) : v, anames)...),
            e.args[2]))
    elseif length(e.args) == 1 && issymbol(e.args[1])
        expand_forms(Expr(:function, Symbol("@", e.args[1])))
    else
        error("invalid macro definition")
    end
end

function expand_lambda(e)
    ex = Expr(:lambda, map(expand_forms, e.args[1]))
    length(e.args) == 2 && push!(ex.args, ())
    for i = 2:length(e.args)
        push!(ex.args, expand_forms(e.args[i]))
    end
    ex
    # Expr(:lambda, 
    #     map(expand_forms, e.args[1]),
    #     (length(e.args) == 2 ? [()] : ())...,
    #     map(expand_forms, e.args[2:end])...)
end

function expand_block(e::Expr)
    if isempty(e.args)
        nothing
    elseif length(e.args) == 1 && !islinenum(e.args[1])
        expand_forms(e.args[1])
    else
        expand_args_forms(e)
    end
end


function _expand_for_nest(lhss, itrs, body, copied_vars, i)
    i > length(lhss) && return body
    coll = make_ssavalue()
    next = gensy()
    state = make_ssavalue()
    outer = isouter(lhss[i])
    lhs = outer ? lhss[i].args[1] : lhss[i]
    body = block(!outer ? map(v -> Expr(:local, v), lhs_vars(lhs)) : (),
        lower_tuple_assignment([lhs, state], next),
        _expand_for_nest(lhss, itrs, body, copied_vars, i + 1))

    body = if i > length(lhss)
        Expr(:var"break-block", :var"loop-cont", Expr(:soft_let, block(map(v -> make_assignment(v, v), copied_vars)...), body))
    else
        scope_block(body)
    end

    block(
        make_assignment(coll, itrs[i]),
        Expr(:local, next),
        make_assignment(next, call(top(:iterate), coll)),
        (if outer
            (Expr(:var"require-existing-local", lhs))
        else
            ()
        end)...,
        Expr(:if, call(top(:not_int), call(core(:(===)), next, nothing)),
            Expr(:_do_while, block(body,
                make_assignment(next, call(top(:iterate), coll, state)),
                call(top(:not_int), call(core(:(===)), next, nothing))
            ))
        )
    )
end

function expand_for(e)
    ranges = if e.args[1].head === :block
        e.args[1].args
    else
        [e.args[1]]
    end
    lhss, iters = [], []
    for r in ranges
        push!(lhss, r.args[1])
        push!(iters, r.args[2])
    end
    ex = expand_for(lhss, iters, e.args[2])
    expand_forms(ex)
end

function expand_for(lhss, iters, body)
    copied_vars = unique(filter(x -> !isunderscore_symbol(x), vcat(map(lhs_vars, filter(!isouter, lhss[1:end-1])))))

    Expr(:var"break-block",
        :var"loop-exit",
        _expand_for_nest(lhss, iters, body, copied_vars, 1)
    )
end

function expand_vect(e)
    has_parameters(e.args) && error("unexpected semicolon in array expression")
    any(isassignment, e.args) && error("misplaced assignment in $(deparse(e))")
    expand_forms(Expr(:call, top(:vect), e.args))
end

function expand_hcat(e)
    any(isassignment, e.args) && error("misplaced assignment in $(deparse(e))")
    expand_forms(Expr(:call, top(:hcat), e.args))
end

function expand_vcat(e)
    a = e.args
    any(isassignment, a) && error("misplaced assignment statement in \"$(deparse(e))\"")
    if has_parameters(a)
        error("unexpected semicolon in array expression")
    else
        expand_forms(
            if any(x -> x isa Expr && x.head == :row, a)
                rows = map(x -> x isa Expr && x.head == :row ? x.args : [x], a)
                call(top(:hvcat), Expr(:tuple, map(length, rows)), vcat(rows...))
            else
                call(top(:vcat), a...)
            end
        )
    end
end

function expand_typed_hcat(e)
    any(isassignment, e.args[2:end]) && error("misplaced assignment statement in \"$(deparse(e))\"")
    expand_forms(call(top(:typed_hcat), e.args...))
end

function expand_typed_vcat(e)
    t = e.agrs[1]
    a = e.args[2:end]
    any(isassignment, a) && error("misplaced assignment statement in \"$(deparse(e))\"")
    expand_forms(
        if any(x -> x isa Expr && x.head === :row, a)
            rows = map(x -> x isa Expr && x.head == :row ? x.args : [x], a)
            call(top(:typed_vcat), t, Expr(:tuple, map(length, rows)), vcat(rows...))
        else
            call(top(:typed_vcat), t, a...)
        end)
end

function expand_generator(e)
    check_no_return(e)
    expand_generator(e, false, [])
end

function expand_generator(e, flat, outervars)
    expr = e.args[1]
    isfilt = e.args[2].head === :filter
    range_exprs = isfilt ? e.args[2].args[2:end] : e.args[2:end]
    ranges = map(x -> x.args[2], range_exprs)
    iter = length(ranges) == 1 ? first(ranges) : call(top(:product), ranges...)
    iter = isfilt ? call(top(:Filter), func_for_generator_ranges(e.args[2].args[1], range_exprs, false, [])) : iter
    gen = call(top(:Generator), func_for_generator_ranges(expr, range_exprs, flat, outervars), iter)

    expand_forms(flat ? call(top(:Flatten), gen) : gen)
end


function func_for_generator_ranges(expr, range_exprs, flat, outervars)
    vars = map(x->x.args[1], range_exprs)
    argname = length(vars) == 1 && issymbol(first(vars)) ? first(vars) : gensy()
    myvars = lhs_vars(Expr(:tuple, vars...))
    splat = if argname == first(vars)
        ()
    elseif length(vars) == 1
        (map(v -> Expr(:local, v), myvars)..., make_assignment(first(vars), argname))
    else
        (map(v -> Expr(:local, v), myvars)..., make_assignment(Expr(:tuple, vars...), argname))
    end
    if expr == argname
        top(:identity)
    elseif isempty(splat) &&
        expr isa Expr && length(expr.args) == 2 && expr.head == :call &&
        expr.args[1] == argname &&
        !isdotop_named(expr.args[1]) &&
        !expr_contains_eq(argname, expr.args[1])
        expr.args[1]
    else
        expr = if flat && expr isa Expr && expr.head === :generator
            expand_generator(expr, false, union(outervars, myvars))
        elseif flat && expr isa Expr && expr.head === :flatten
            expand_generator(expr.args[1], true, union(outervars, myvars))
        elseif !isempty(outervars)
            Expr(:let, block( map(v -> make_assignment(v, v), filter(!isunderscore_symbol, outervars))...), expr)
        else
            expr
        end
        Expr(:->, argname, block(splat..., expr))
    end
end


expand_break(e) = e isa Expr ? e : Expr(:break, :var"loop-exit")


expand_continue(e) = Expr(:break, :var"loop-cont")


function expand_while(e)
    Expr(:var"break-block", :var"loop-exit",
        Expr(:_while, expand_forms(e.args[1]),
            Expr(:var"break-block", :var"loop-cont",
                Expr(:var"scope-block", blockify(
                    expand_forms(e.args[2]))))))
end



function expand_gc_preserve(e)
    s = make_ssavalue()
    r = make_ssavalue()
    Expr(:block,
        Expr(:(=), s, gc_preserve_begin(e.args[1].args)),
        Expr(:(=), r, expand_forms(e.args[1])),
        gc_preserve_end(s),
        r)
end

function expand_line(e)
    global current_desugar_loc = e
    e
end

function expand_if(e)
    test = e.args[1]
    blk = test isa Expr && test.head == :block
    stmts = blk ? test.args[1:end-1] : []
    test = blk ? last(test.args) : test
    if test isa Expr && test.head == :&&
        clauses = Expr(:&&, map(expand_forms, flatten_ex(:&&, test).args)...)
        Expr(:if, (blk ? Expr(:block, map(expand_forms, stmts)..., clauses) : clauses),
            map(expand_forms, e.args[2:end])...)
    else
        expand_args_forms(e)
        # Expr(e.head, map(expand_forms, e.args)...)
    end
end

function expand_const_decl(e)
    arg = e.args[1]
    if isatom(arg)
        e
    else
        if arg.head in (:global, :local, :var"local-def")
            foreach(b -> !isassignment(b) && error("expected assignment after \"const\""), arg.args)
            expand_forms(expand_delcs(arg.head, arg.args, true))
        elseif arg.head in (:(=), :(::))
            expand_forms(expand_decls(:const, e.args, false))
        else
            e
        end
    end
end

function expand_local_or_global_decl(e)
    if issymbol(e.args[1]) && length(e.args) == 1
        e
    else
        expand_forms(expand_decls(e.head, e.args, false))
    end
end

function expand_try(e)
    tryb = e.args[1]
    var = e.args[2]
    catchb = e.args[3]
    if length(e.args) == 4
        has_unmatched_symbolic_goto(tryb) && error("goto from a try/finally block is not permitted")
        finalb = e.args[4]
        expand_forms(Expr(:tryfinally, catchb !== false ? Expr(:try, tryb, var, catchb) : scope_block(tryb), scope_block(finalb)))
    elseif length(e.args) == 3
        expand_forms(
            if issymbol_like(var)
                Expr(:trycatch, scope_block(tryb),scope_block(block(make_assignment(var, Expr(:the_exception)), catchb)))
            else
                Expr(:trycatch, scope_block(tryb), scope_block(catchb))
            end
        )
    else
        error("invalid try form")
    end
end

function expand_decls(what, binds, isconst)
    !(binds isa Vector) && error("invalid $what declaration")
    vars, assigns = [], []

    for x in binds
        if assignment_like(x) || isfunction_def(x)
            append!(vars, lhs_decls(assigned_name(x.args[1])))
            push!(assigns, Expr(x.head, all_decl_vars(x.args[1]), x.args[2]))
        elseif x isa Expr && x.head == :(::)
            push!(vars, decl_var(x))
            push!(assigns, Expr(:decl, x.args...))
        elseif issymbol(x)
            push!(vars,x)
        else
            error("invalid syntax in $what declaration")
        end
    end

    block((isconst ? map(x -> Expr(:const, x), vars) : ())..., 
        map(x -> Expr(what, x), vars)...,
        assigns)
end

function expand_decl(e)
    length(e.args) !== 2 && error("invalid :: syntax")
    if !issymbol_like(e.args[1])
        call(core(:typeassert), expand_forms(e.args[1]), expand_forms(e.args[2]))
    else
        e = Expr(e.head, expand_forms(e.args[1]), expand_forms(e.args[2]))
    end    
end

function expand_ref(e)
    args = e.args[2:end]
    has_parameters(args) && error("unexpected semicolon in array expression")
    expand_forms(partially_expand_ref(e))
end

function partially_expand_ref(e)
    a = e.args[1]
    idxs = e.args[2:end]
    reuse = a isa Expr && contains(x -> x == :begin || x == :end, idxs)
    arr = reuse ? make_ssavalue() : a
    stmts = reuse ? make_assignment(arr, a) : ()
    new_idxs, stuff = process_indices(arr, idxs)
    block(vcat(stmts, stuff)..., call(top(:getindex), arr, new_idxs...))
end

function expand_curly(e)
    has_parameters(e.args[2:end]) && error("unexpected semicolon in array expression")
    any(isassignment, e.args[2:end]) && error("misplaced assignment statement in $(deparse(e))")
    p = extract_implicit_whereparams(e)
    curlyparams = p[1]
    whereparams = p[2]
    if isempty(whereparams)
        expand_forms(call(core(:apply_type), e.args...))
    else
        expand_forms(Expr(:where, Expr(:curly, e.args[1], curlyparams...), whereparams...))
    end
end

function expand_do(e)
    _call = e.args[1]
    f = _call.args[1]
    argl = _call.args[2:end]
    af = e.args[2]
    expand_forms(if has_parameters(argl)
        call(f, argl[1], af, argl[2:end])
    else
        call(f, af, argl...)
    end)
end

function expand_tuple(e)
    if length(e.args) > 0 && e.args[1] isa Expr && e.args[1].head === :parameters
        if length(e.args) == 1
            expand_forms(lower_named_tuple(e.args[1].args))
        else
            error("unexpected semicolon in tuple")
        end
    elseif any(isassignment, e.args)
        expand_forms(lower_named_tuple(e.args))
    else
        expand_forms(call(core(:tuple), e.args...))
    end
end

function expand_string(e)
    expand_forms(call(top(:string), map(s -> s isa Expr && s.head === :string ? s.args[1] : s, e.args)...))
    top
end

function expand_call(e)
    if length(e.args) > 1
        f = e.args[1]
        if isdotop_named(f)
            expand_fuse_broadcast((), Expr(:., undotop(f), Expr(:tuple, e.args[2:end]...)))
        elseif f isa Expr && length(f.args) == 1 && f.head == :.
            expand_fuse_broadcast((), Expr(:., f.args[1], Expr(:tuple, e.args[2:end]...)))
        elseif f === :ccall
            length(e.args) < 4 && error("too few arguments to ccall")
            cconv = e.args[3]
            have_cconv = cconv in (:cdecl, :stdcall, :fastcall, :thiscall, :llvmcall)
            after_cconv = have_cconv ? e.args[5:end] : e.args[4:end]
            name = e.args[2]
            RT = after_cconv[1]
            argtypes = after_cconv[2]
            args = after_cconv[3:end]
            if !(argtypes isa Expr && argtypes.head === :tuple)
                if RT isa Expr && RT.head === :tuple
                    error("ccall argument types must be a tuple; try \"(T,)\" and check if you specified a correct return type")
                else
                    error("ccall argument types must be a tuple; try \"(T,)\"")
                end
            end
            expand_forms(lower_ccall(name, RT, argtypes[2:end], args, have_cconv ? cconv : :ccall))
        elseif any(iskwarg, e.args[2:end])
            expand_forms(lower_kw_call(f, e.args[2:end]))
        elseif has_parameters(e.args[2:end])
            expand_forms(if isempty(e.args[2].args)
                call(f, e.args[3:end])
            else
                lower_kw_call(f, e.args[2:end])
            end)
        elseif any(isvararg, e.args[2:end])
            argl = e.args[2:end]
            function tuple_wrap(argl, run, i = 1)
                if i > length(argl)
                    isempty(run) ? [] : [call(core(:tuple), run...)]
                else
                    x = argl[i]
                    if x isa Expr && x.head === :...
                        if isempty(run)
                            [x.args[1]; tuple_wrap(argl, [], i + 1)]
                        else
                            [call(core(:tuple), run...); x.args[1]; tuple_wrap(argl, [], i + 1)]
                        end
                    else
                        push!(run, x)
                        tuple_wrap(argl, run, i + 1)
                    end
                end
            end
            expand_forms(call(core(:_apply_iterate), top(:iterate), f, tuple_wrap(argl, [])...))
        elseif identifier_name(f) == :^ && length(e.args) == 3 && isinteger(e.args[3])
            expand_forms(call(top(:literal_pow), f, e.args[2], call(call(core(:apply_type), top(:Val)), e.args[3])))
        else
            expand_args_forms(e)
            # Expr(:call, map(expand_forms, e.args)...)   
        end
    else
        # map(expand_forms, e)
        call(map(expand_forms, e.args)...)   
        # call(expand_forms(e.args[1]))
    end
end

function lower_kw_call(f, args)
    para = has_parameters(args) ? args[1].args : []
    args = has_parameters(args) ? args[2:end] : args
    parg_stmts = remove_argument_side_effects(call(f, args...))
    call_ex = parg_stmts[1] # todo: not sure of structure
    fexpr = call_ex.args[1] # todo: not sure of structure
    cargs = call_ex.args[2:end]
    
    kws, pargs = separate(iskwarg, cargs)
    block(
        parg_stmts.args...,
        lower_kw_call_(fexpr, vcat(kws, para), pargs)
        )
end

function lower_kw_call_(fexpr, kw, pa)
    function kw_call_unless_empty(f, pa, kw_container_test, kw_container)
        Expr(:if, call(top(:isempty), kw_container_test), 
            call(f, pa...),
            call(call(core(:kwfunc), f), kw_container, f, pa...))
    end

    f = issym_ref(fexpr) ? fexpr : make_ssavalue()
    kw_container = make_ssavalue()
    block(
        (f == fexpr ? () : make_assignment(f, fexpr))...,
        make_assignment(kw_container, lower_named_tuple(kw, name -> "keyword argument $name repeated in call to $(deparse(fexpr))", "keyword argument", "keyword argument syntax")),
        (all(isvararg, kw) ? kw_call_unless_empty(f, pa, kw_container, kw_container) : call(call(core(:kwfunc), f), kw_container, f, pa...))
    )
end

function lower_tuple_assignment(lhss, x)
    t = make_ssavalue()
    function _loop(lhss, i = 1)
        if i > length(lhss)
            []
        else
            out = []
            if eventually_call(lhss[i])
                temp = gensy()
                push!(out, block(
                    local_def(temp),
                    make_assignment(temp, call(core(:getfield), t, i)),
                    make_assignment(lhss[i], temp)
                ))
            else
                push!(out, make_assignment(lhss[i], call(core(:getfield), t, i)))
            end
            for x in _loop(lhss, i + 1)
                push!(out, x)
            end
            out
            # vcat(if eventually_call(lhss[i])
            #     temp = gensy()
            #     block(
            #         local_def(temp),
            #         make_assignment(temp, call(core(:getfield), t, i)),
            #         make_assignment(lhss[i], temp)
            #     )
            # else
            #     make_assignment(lhss[i], call(core(:getfield), t, i))
            # end, _loop(lhss, i + 1))
        end
    end
    block(
        make_assignment(t, x),
        (_loop(lhss, 1))...,
        t
    )
end

function expand_comprehension(e)
    if length(e.args) > 1
        expand_forms(Expr(:comprehension, Expr(:generator, e.args...)))
    else
        e.args[1].head == :generator && any(x -> x == :(:), e.args[1].args[2:end]) && error("comprhension syntax with `:` ranges has been removed")
        expand_forms(call(top(:collect), e.args[1]))
    end
end

function expand_typed_comprehension(e)
    expand_forms(
        if e.args[2].head === :generator && let ranges = e.args[2].args[2:end];
            any(==(:(:)), ranges) && error("comprhension syntax with `:` ranges has been removed")
            all(x -> x isa Expr && x.head === :(=), ranges)
            end
            lower_comprehension(e.args[1], e.args[2].args[1], e.args[2].args[2:end])
        else
            call(top(:collect), e.args[1], e.agrs[2])
        end
    )
end

function lower_comprehension(ty, expr, itrs)
    check_no_return(expr)
    has_break_or_continue(expr) && error("break or continue outside loop")
    result = gensy()
    idx = gensy()
    oneresult = make_ssavalue()
    prod = make_ssavalue()
    isz = make_ssavalue()
    szunk = make_ssavalue()
    iv = map(x -> make_ssavalue(), itrs)

    function construct_loops(itrs, iv, i = 1)
        if i > length(itrs)
            block(
                make_assignment(oneresult, expr),
                Expr(:inbounds, true),
                if szunk
                    call(top(:push!), result, oneresult)
                else
                    call(top(:setindex!), result, oneresult, idx)
                end,
                Expr(:inbounds, :pop),
                make_assignment(idx, call(top(:add_int), idx, 1))
            )
        else
            Expr(:for, make_assignment(itrs[i], iv[i]), construct_loops(itrs, iv, i + 1))    
        end
    end

    overall_itr = length(itrs) == 1 ? first(iv) : prod
    scope_block(block(
        Expr(:local, result), Expr(:local, idx),
        map((v,r) -> make_assignment(v, r.args[2]), iv, itrs),
        length(itrs) == 1 ? () : make_assignment(prod, call(top(:product), iv...)),
        make_assignment(isz, call(top(:IteratorSize), overall_itr)),
        make_assignment(szunk, call(core(:isa), isz, top(:SizeUnknown))),
        Expr(:if, szunk, 
            make_assignment(result, call(Expr(:curly, core(:Array), ty, 1), core(:undef), 0)),
            make_assignment(result, call(top(:_array_for), ty, overall_itr, isz))
        ),
        make_assignment(idx, call(top(:first), call(top(:LinearIndices), result))),
        construct_loops(itrs, iv),
        result
    ))
end


function comp_accum(e::Vector, make_and, isdone, take, expr = nothing)
    if isdone(e)
        (expr, e)
    else
        ex_rest = take(e)
        comp_accum(ex_rest[2], make_and, isdone, take, if expr === nothing
        first(ex_rest) 
        else
            make_and(expr, first(ex_rest))     
        end)
    end
end

function add_init(arg, arg2, expr)
    if arg == arg2
        expr
    else
        Expr(:block, Expr(:(=), arg2, arg), expr)
    end
end

function compare_one(e::Vector)
    arg = e[3]
    arg2 = ispair(arg) && ispair(e[3]) ? make_ssavalue() : arg
    if !isdotop_named(e[1]) && 
        length(e) == 5 && 
        ispair(e[4]) && 
        isdotop_named(e[5])
        s = make_ssavalue()
        (block(
            (arg == arg2 ? () : make_assignment(arg2, arg))...,
            make_assignment(s, e[5])
        ))
    else
        (add_init(arg, arg2, Expr(:call, e[2], e[1], arg2)), e[3:end])
    end
end

function expand_scalar_compare(e::Vector)
    comp_accum(e,
        (a,b) -> Expr(:&&, a, b),
        x -> !(length(x) > 1) || isdotop_named(x[1]),
        compare_one)
end

function expand_vector_compare(e::Vector)
    comp_accum(e, 
        (a,b) -> call(:(.&), a, b), 
        x -> !(length(x) > 1), 
        e -> isdotop(e[1]) ? compare_one(e) : expand_scalar_compare(e))
end

expand_compare_chain(e::Vector) = expand_vector_compare(e)[1]

function end_val(a, n, tuples, last)
    if isempty(tuples)
        if last && n == 1
            call(Expr(:top, :lastindex), a)
        else
            call(Expr(:top, :lastindex), a, n)
        end
    else
        dimno = call(Expr(:top, :+), n -  length(tuples), map(t -> call(Expr(:top, :length), t), tuples))
        call(Expr(:top, :lastindex), a, dimno)
    end
end

function begin_val(a, n, tuples, last)
    if isempty(tuples)
        if last && n == 1
            call(Expr(:top, :firstindex), a)
        else
            call(Expr(:top, :firstindex), a, n)
        end
    else
        dimno = call(Expr(:top, :+), n - length(tuples), map(t -> call(Expr(:top, :length), t), tuples))
        call(Expr(:top, :first), call(Expr(:top, :axes), a, dimno))
    end
end

function replace_beginend(ex, a, n, tuples, last)
    if ex === :end
        end_val(a, n, tuples, last)
    elseif ex === :begin
        begin_val(a, n, tuples, last)
    elseif isatom(ex) || isquoted(ex)
        ex
    elseif ex.head === :ref
        # Expr(:ref, replace_beginend(ex.args[1], a, n, tuples, last), ex.args[2:end]...) 
        ex.args[1] = replace_beginend(ex.args, a, n, tuples, last)
        ex
    else
        Expr(ex.head, map(x -> replace_beginend(x, a, n, tuples, last), ex.args)...)
    end
end

function process_indices(a, i)
    n = 1
    ret, stmts, tuples = [], [], []
    for idx in i
        islast = idx == last(i)
        if ispair(idx) && idx.head === :...
            if issymbol_like(idx.args[1])
                push!(tuples, idx.args[1])
                push!(ret, Expr(:..., replace_beginend(idx.args[1], a, n, tuples, islast)))
            else
                g = make_ssavalue()
                push!(stmts, Expr(:(=), g, replace_beginend(idx.args[1], a, n, tuples, islast)))
                push!(tuples, g)
                push!(ret, Expr(:..., g))
            end
        else
            push!(ret, replace_beginend(idx, a, n, tuples, islast))
        end
        n += 1
    end
    ret, stmts
end


function analyze_typevar(e)::Tuple
    check_sym(s) = issymbol(s) ? s : error("invalid type parameter name $(deparse(s))")
    if isatom(e)
        (check_sym(e), false, false)
    elseif e.head == :var"var-bounds"
        e.args[1]
    elseif e.head === :comparison && length(e.args) == 5
        if e.args[2] == :<: && e.args[4] == :<:
            (check_sym(e.args[3]), e.args[1], e.args[5])
        else
            error("invalid bounds in \"where\"")
        end
    elseif e.head == :<:
        (check_sym(e.args[1]), false, e.args[2])
    elseif e.head == :>:
        (check_sym(e.args[1]), e.args[2], false)
    else
        error("invalid variable expression in \"where\"")
    end
end



function unmangled_name(v)
    if v ==  :var""
        v
    else
        s = string(v)
        if first(s) == '#'
            Symbol(last(split(s, '#')))
        else
            v
        end
    end
end

function bounds_to_TypeVar(v, unmangle = false)
    # v is Expr or list?
    lb = v[2]
    ub = v[3]
    uv = unmangle ? unmangled_name(v[1]) : v[1]
    if ub !== false
        if lb !== false
            call(Expr(:core, :TypeVar), uv, lb, ub)
        else
            call(Expr(:core, :TypeVar), uv, ub)
        end
    else
        if lb !== false
            call(Expr(:core, :TypeVar), uv, lb, Expr(:core, :Any))
        else
            call(Expr(:core, :TypeVar), uv)
        end
    end
end

function method_expr_name(m)
    name = m.args[1]
    if name isa Expr && name.head === :outerref
        name.args[1]
    else
        name
    end
end

function method_expr_static_parameters(m)
    type_ex = m.args[2]
    if type_ex.head === :block
        # Indexing here is wrong
        sp_ssavals = last(type_ex).args[4].args[3:end]
        map(function (a)
            a.args[2].args[2].args[1]
        end, filter(e -> ispair(e) && e.head == :(=) && e.args[1] in sp_ssavals, type_ex.args))
    else
        []
    end
end

function scopenest(names, vals, expr)
    if isempty(names)
        expr
    else
        Expr(:let, Expr(:(=), popfirst!(names), popfirst!(vals)), 
            Expr(:block, scopenest(names, vals, expr)))
    end
end


function linenode_string(lno)
    # 
    if length(lno) == 2
        string(" around line ", lno.args[1])
    elseif length(lno) == 3
        string(" around ", lno.args[2], ":", lno.args[1])
    end
end


# function lower_ccall(name, RT, atypes, args, cconv)
    
# end

function flatten_all_where_expr(e)
    if e isa Expr && e.head == :where
        flatten_where_expr(e)
    elseif e isa Expr
        ex = Expr(e.head)
        for a in e.args
            push!(ex.args, flatten_all_where_expr(a))
        end
        ex
    else
        e
    end
end

function flatten_where_expr(e, vars = [])
    if e isa Expr && e.head === :where
        for i = length(e.args):-1:2
            push!(vars, e.args[i])
        end
        flatten_where_expr(e.args[1], vars)
    else
        Expr(:where, e, vars...)
    end
end

function expand_where(body, var)
    bounds = analyze_typevar(var)
    v = bounds[1]
    Expr(:let, Expr(:(=), v, bounds_to_TypeVar(bounds)),
        call(core(:UnionAll), v, body))
end

function expand_wheres(body, vars)
    if isempty(vars)
        body
    else
        w = pop!(vars)
        expand_where(expand_wheres(body, vars), w)
    end
end

function sink_assignment(lhs, rhs)
    if rhs isa Expr && rhs.head === :block
        block(rhs.args[1:end-1]..., make_assignment(lhs, rhs.args[end]))
    else
        Expr(:(=), lhs, rhs)
    end
end


function expand_forms(e)
    if isatom(e) || e.head in (:quote, :inert, :top, :core, :globalref, :outerref, :module, :toplevel, :ssavalue, :null, :true, :false, :meta, :using, :import, :export, :thismodule, :var"toplevel-module")
        e
    else
        if haskey(expand_table, e.head)
            expand_table[e.head](e)
        else
            expand_args_forms(e)
        end
    end
end

const expand_table = Dict(
    :function => expand_function_def,
    :-> => expand_arrow,
    :let => expand_let,
    :var"soft-let" => e -> expand_let(e, false),
    :macro => expand_macro_def,
    :struct => expand_struct_def,
    :try => expand_try,
    :lambda => expand_lambda,
    :block => expand_block,
    :. => expand_dot,
    :(.=) => expand_dot_eq,
    :<: => expand_subtype,
    :>: => expand_supertype,
    :--> => expand_arrow,
    :where => e -> expand_forms(expand_wheres(e.args[1], e.args[2:end])),
    :const => expand_const_decl,
    :local => expand_local_or_global_decl,
    :global => expand_local_or_global_decl,
    :var"local-def" => expand_local_or_global_decl,
    :(=) => expand_eq,
    :abstract => expand_abstract,
    :primitive => expand_primitive,
    :comparison => e -> expand_forms(expand_compare_chain(e.args)),
    :ref => expand_ref,
    :curly => expand_curly,
    :call => expand_call,
    :do => expand_do,
    :tuple => expand_tuple,
    :braces => e -> error("{ } vector syntax is discontinued"),
    :braces_cat => e -> error("{ } matrix syntax is discontinued"),
    :string => expand_string,
    :(::) => expand_decl,
    :if => expand_if,
    :elseif => expand_if,
    :while => expand_while,
    :break => expand_break,
    :continue => expand_continue,
    :for => expand_for,
    :&& => expand_and,
    :|| => expand_or,
    :& => e -> error("invalid syntax $(deparse(e))"),
    :+= => lower_update_op,
    :-= => lower_update_op,
    :(*=) => lower_update_op,
    :.*= => lower_update_op,
    :/= => lower_update_op,
    :./= => lower_update_op,
    ://= => lower_update_op,
    :.//= => lower_update_op,
    :\= => lower_update_op,
    :.\= => lower_update_op,
    :.+= => lower_update_op,
    :.-= => lower_update_op,
    :^= => lower_update_op,
    :.^= => lower_update_op,
    :÷= => lower_update_op,
    :.÷= => lower_update_op,
    :%= => lower_update_op,
    :.%= => lower_update_op,
    :|= => lower_update_op,
    :.|= => lower_update_op,
    :&= => lower_update_op,
    :.&= => lower_update_op,
    :$= => lower_update_op,
    :⊻= => lower_update_op,
    :.⊻= => lower_update_op,
    :<<= => lower_update_op,
    :.<<= => lower_update_op,
    :>>= => lower_update_op,
    :.>>= => lower_update_op,
    :>>>= => lower_update_op,
    :.>>>= => lower_update_op,
    :... => e -> error("... expression outside call"),
    :$ => e -> error("\$ expression outside quote"),
    :vect => expand_vect,
    :hcat => expand_hcat,
    :vcat => expand_vcat,
    :typed_hcat => expand_typed_hcat,
    :typed_vcat => expand_typed_vcat,
    :generator => expand_generator,
    :flatten => e -> expand_generator(e.args[1], true, []),
    :comprehension => expand_comprehension,
    :typed_comprehension => expand_typed_comprehension,
    :gc_preserve => expand_gc_preserve,
    :line => expand_line
)

