function expand_arrow(e)
    a = e.args[1]
    body = e.args[2]
    where = if a isa Expr && a.head === :where
        w = flatten_where_expr(a)
        a = w.args[1]
        w.args[2:end]
    else
        false
    end
    argl = if a isa Expr
        tuple_to_arglist(Expr(a.head, filter(!islinenum, a.args)...))
    else
        [a]
    end
    name = Symbol("#", current_julia_module_counter())
    expand_forms(Expr(:block, Expr(:local, name),
        Expr(:function,
        if where !== false
            Expr(:where, call(name, argl), where...)
        else
            call(name, argl...)
        end,
        body)))
end


function expand_dot(e)
    if length(e.args) == 1
        Expr(:call, top(:BroadcastFunction), e.args[1])
    else
        expand_fuse_broadcast([], e)
    end
end

expand_dot_eq(e::Expr) = expand_fuse_broadcast(e.args[1], e.args[2])

expand_subtype(e::Expr) = expand_forms(Expr(:call, :<:, e.args...))

expand_supertype(e::Expr) = expand_forms(Expr(:call, :>:, e.args...))

function expand_fuse_broadcast(lhs, rhs)
    isfuse(e) = e isa Expr && e.head === :fuse
    function dot_to_fuse(e, istop = false)
        function make_fuse(f, args::Vector)
            kws, args = split_kwargs(args)
            kws = isempty(kws) ? kws : [Expr(:parameters, kws...)]
            args = map(dot_to_fuse, args)
            make = call(top(isempty(kws) ? :broadcasted : :broadcasted_kwsyntax), kws..., f, args...)
            istop ? Expr(:fuse, make) : make
        end

        if e isa Expr && length(e.args) == 2 && e.head === :.
            f = e.args[1]
            x = e.args[2]
            if isatom(x) || x.head in (:quote, :inert, :$)
                call(top(:getproperty), f, x)
            elseif x.head === :tuple
                if identifier_name(f) == :^ && length(x.args) == 2 && isinteger(x.args[2])
                    make_fuse(top(:literal_pow), [f, x.args[1], expand_forms(call(core(:apply_type), top(:Val), x.args[2]))])
                else
                    make_fuse(f, x.args)
                end
            else
                error("invalid syntax\"$(deparse(e))\"")
            end
        else
            if e isa Expr && e.head === :call
                function make_fuse_(f, x)
                    
                end
                f = e.args[1]
                if isdotop_named(f)
                    make_fuse_(undotop(f), e.args[2:end])
                elseif f isa Expr && f.head === :. && length(f.args) == 1
                    # todo: assume this is deprecated?
                    make_fuse_(f.args[1], e.args[2:end])
                else
                    e
                end
            else
                e
            end
        end
    end
    e = dot_to_fuse(rhs, true)
    lhs_view = ref_to_view(lhs)
    
    if isfuse(e)
        if isempty(lhs)
            expand_forms(call(top(:materialize), e.args...))
        else
            expand_forms(call(top(:materialize!), lhs_view, e.args...))
        end
    else
        if isempty(lhs)
            expand_forms(e)
        else
            expand_forms(call(top(:materialize!), lhs_view, call(top(:broadcasted), top(:identity), e)))
        end
    end
end

function split_kwargs(args::Vector)::Tuple{Vector,Vector}
    kwargs, pargs = [], []
    for i = 1:length(args)
        arg = args[i]
        if i == 1 && arg isa Expr && arg.head === :parameters
            for j in 1:length(arg.args)
                push!(kwargs, arg.args[j])
            end
        end
        if iskwarg(arg)
            push!(kwargs, arg)
        else
            push!(pargs, arg)
        end
    end

    kwargs, pargs
end

function ref_to_view(expr)
    if expr isa Expr && expr.head === :ref
        ex = partially_expand_ref(expr)
        stmts = ex.args[1:end-1]
        refex = last(ex.args)
        nuref = call(top(:dotview), refex.args[2], refex.args[3:end])
        block(stmts..., nuref)
    else
        expr
    end
end


function expand_eq(e)
    lhs = e.args[1]
    function isfunction_lhs(lhs)
        lhs isa Expr && 
            (lhs.head === :call || 
                lhs.head === :where ||
                (lhs.head === :(::) && lhs.args[1] isa Expr && lhs.args[1].head === :call))
    end
    assignment_to_function(lhs, e) = Expr(:function, e.args...)

    if isfunction_lhs(lhs)
        expand_forms(assignment_to_function(lhs, e))
    elseif iscurly(lhs)
        expand_unionall_def(lhs, e.args[2])
    elseif isassignment(e.args[2])
        function chain_assign_loop(lhss, rhs)
            if isassignment(rhs) && !isfunction_lhs(rhs.args[1])
                push!(lhss, rhs.args[1])
                chain_assign_loop(lhss, rhs.args[2])
            else
                rr = issymbol_like(rhs) ? rhs : make_ssavalue()
                expand_forms(Expr(:block, (if rr == rhs
                    ()
                else
                    if isassignment(rhs)
                        assignment_to_function(rhs.args[1], rhs)
                    else
                        [rhs]
                    end
                end)...,
                map(l -> Expr(:(=), l, rr), lhss)...,
                Expr(:unnecessary, rr)))
            end
        end

        chain_assign_loop([lhs], e.args[2])
    elseif (issymbol_like(lhs) && isvalid_name(lhs)) || isglobalref(lhs) || isouterref(lhs)
        sink_assignment(lhs, expand_forms(e.args[2]))
    elseif isatom(lhs)
        error("invalid assignment location $(deparse(lhs))")
    else
        if lhs.head == :.
            a = lhs.args[1]
            b = lhs.args[2]
            rhs = e.args[2]
            if b isa Expr && b.head === :tuple && length(b.args) == 1
                error("invalid syntax") # todo
            end
            aa = issymbol_like(a) ? a : make_ssavalue()
            bb = isatom(b) || issymbol_like(b) || (b isa Expr && isquoted(b)) ? b : make_ssavalue()
            rr = issymbol_like(rhs) || isatom(rhs) ? rhs : make_ssavalue()
            Expr(:block,
                aa == a ? [] : [sink_assignment(aa, expand_forms(a))],
                bb == b ? [] : [sink_assignment(bb, expand_forms(b))],
                rr == rhs ? [] : [sink_assignment(rr, expand_forms(rhs))],
                call(top(:setproperty!), aa, bb, rr),
                Expr(:unnecessary, rr))
        elseif lhs.head === :tuple #L2081
            lhss = lhs.args
            x = e.args[2]
            function sides_match(l, r)
                if isempty(l)
                    isempty(r)
                elseif isvararg(first(l))
                    true
                elseif isempty(r)
                    false
                elseif isvararg(first(r))
                    length(r) == 1
                else
                    sides_match(l[2:end], r[2:end])
                end
            end

            if x isa Expr && !isempty(lhss) && x.head === :tuple && !(any(isassignment, x.args)) &&
                !has_parameters(x.args) &&
                sides_match(lhss, x.args)
                expand_forms(tuple_to_assignments(lhss, x))
            else
                function isin_lhs(x, lhss)
                    for l in lhss
                        if l isa Expr && l.head === :...
                            if l == last(lhss)
                                return l.args[1] == x
                            else
                                error("invalid ... on non-final assignment location")
                            end
                        elseif l == x
                            return true
                        end
                    end
                    false
                end

                xx = (!isin_lhs(x, lhss) && issymbol(x)) || isssavalue(x) ? x : make_ssavalue()
                ini = x == xx ? [] : [sink_assignment(xx, expand_forms(x))]
                n = length(lhss)
                n = if n > 0
                    l = last(lhss)
                    if isvararg(l) && isunderscore_symbol(l.args[1])
                        n -1 
                    else
                        n
                    end
                else
                    n
                end
                st = gensy()
                
                Expr(:block,
                    (n > 0 ? [Expr(:local, st)] : ())...,
                    ini...,
                    map((i, lhs) -> expand_forms(if isvararg(lhs)
                        Expr(:(=), lhs.args[1], call(top(:rest), xx, (i == 1 ? () : [st])...))
                    else
                        lower_tuple_assignment(if i == n
                            [lhs]
                    else
                        [lhs, st]
                        end, Expr(:call, top(:indexed_iterate), xx, i, (i == 1 ? () : [st])...))
                    end), 1:n, lhss)...,
                    Expr(:unnecessary, xx))
            end
        elseif lhs.head === :typed_hcat
            error("invalid spacing in left side of indexed assignment")
        elseif lhs.head === :typed_vcat
            error("unexpected \";\" in left side of indexed assignment")
        elseif lhs.head === :ref
            a = lhs.args[1]
            idxs = lhs.args[2:end]
            rhs = e.args[2]
            reuse = a isa Expr && contains(x -> x == :end, idxs)
            arr = reuse ? make_ssavalue() : a
            stmts = reuse ? Expr(:(=), arr, expand_forms(a)) : ()
            rrhs = rhs isa Expr && !isssavalue(rhs) && !isquoted(rhs)
            r = rrhs ? make_ssavalue() : rhs
            rini = rrhs ? [(sink_assignment(r, expand_forms(rhs)))] : ()

            new_idxs, stuff = process_indices(arr, idxs)
            Expr(:block,
                stmts...,
                map(expand_forms, stuff)...,
                rini...,
                expand_forms(Expr(:call, top(:setindex!), arr, r, new_idxs...)),
                Expr(:unnecessary, r))
        elseif lhs.head === :(::)
            x = lhs.args[1]
            T = lhs.args[2]
            rhs = e.args[2]
            # todo: what is output of remove_argument_side_effects?
            e = remove_argument_side_effects(x)
            expand_forms(Expr(:block, e[2]..., 
                Expr(:decl, e[1], T),
                Expr(:(=), e[1], rhs)))
        elseif lhs.head === :vcat
            error("use \"(a, b) = ...\" to assign multiple values")
        else
            error("invalid assignment location \"$(deparse(lhs))\"")
        end
    end
end


expand_or(e::Expr) = expand_or(flatten_ex(:||, e).args, 1)

function expand_or(e, i)
    if isempty(e)
        return false
    end
    if i == length(e)
        last(e)
    else
        if issymbol_like(e[i])
            Expr(:if, e[i], e[i], expand_or(e, i + 1))
        else
            g = make_ssavalue()
            Expr(:block, Expr(:(=), g, e[i]), 
                Expr(:if, g, g, expand_or(e, i + 1)))
        end
    end
end

expand_and(e::Expr) = expand_and(flatten_ex(:&&, e).args, 1)
    
function expand_and(e, i)
    if isempty(e)
        return true
    end
    if i == length(e)
        last(e)
    else
        Expr(:if, e[i], expand_and(e, i + 1), false)
    end
end



function lower_update_op(e)
    str = string(e.head)
    expand_forms(expand_update_operator(
            str[1:end-1],
            str[1] == '.' ? :.= : :(=),
            e.args[1],
            e.args[2]
        ))
end

function expand_update_operator(op, opeq, lhs, rhs, declT = nothing)
    if lhs isa Expr && lhs.head == :ref
        ex = partially_expand_ref(lhs)
        stmts = ex.args[1:end-1]
        refex = last(ex.args)
        nuref = Expr(:ref, refex.args[2], refex.args[3:end]...)
        block(stmts..., expand_update_operator_(op, opeq, nuref, rhs, declT))
    elseif lhs isa Expr && lhs.head === :(::)
        e = remove_argument_side_effects(lhs.args[1])
        T = lhs.args[2]
        block(e.args..., expand_update_operator(op, opeq, e[1], rhs, T))
    else
        if lhs isa Expr && opeq == :(=) && !(lhs.head in (:., :tuple, :vcat, :typed_hcat, :typed_vcat))
            error("invalid assignment location \"$(deparse(lhs))\"")
        else
            expand_update_operator_(op, opeq, lhs, rhs, declT)
        end
    end
end

function expand_update_operator_(op, opeq, lhs, rhs, declT)
    e = remove_argument_side_effects(lhs)
    newlhs = e[1]
    temp = opeq == :.= && newlhs isa Expr && newlhs.head !== :ref && make_ssavalue()
    e = if temp === false
        e
    else
        (temp, vcat(e[2], make_assignment(temp, newlhs))) #todo: wrong order?
    end
    newlhs = temp === false ? newlhs : temp
    if lhs isa Expr && lhs.head === :tuple
        for i = 1:length(lhs)
            a = lhs[i]
            b = newlhs[i]
            if a isa Expr
                if isssavalue(a) && !isssavalue(b)
                    error("invalid multiple assignment location \"$(deparse(b))\"")
                end
            else
                break
            end
        end
    end
    block(
        e[2]...,
        if declT === nothing
            Expr(opeq, newlhs, call(op, newlhs, rhs))
        else
            Expr(opeq, newlhs, call(op, Expr(:(::), newlhs, first(declT)), rhs))
        end
    )
end

function expand_unionall_def(name, type_ex)
    if iscurly(name)
        params = name.args[2:end]
        name = name.args[1]
        isempty(params) && error("empty type parameter list in $name")
        block(
            Expr(:var"const-if-global", name), 
            expand_forms(make_assignment(name, Expr(:where, type_ex, params)))
        )
    else
        Expr(:const, make_assignment(name, type_ex))
    end
end

