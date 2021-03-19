function type_for_closure_parameterized(name, P, names, fields, types, super)
    n = length(P)
    s = make_ssavalue()
    [Expr(:thunk, Expr(:lambda, (), [(), (), 0, ()], block(Expr(:global, name), Expr(:const, name),
        map((p,n) -> make_assignment(p, call(core(:TypeVar), n, core(:Any))), P, names)...,
        make_assignment(s, call(core(:_structtype), thismodule(), inert(name), call(core(:svec), P...),
            call(core(:svec), map(quotify, fields)...), false, length(fields))),
        make_assignment(outerref(name), s),
        call(core(:_setsuper!), name, super),
        call(core(:_typebody!), name, call(core(:svec), types...)),
        Expr(:return, nothing)
    )))]
end

function type_for_closure(name, fields, super)
    s = make_ssavalue()
    [Expr(:thunk,Expr(:lambda, (), [(), (), 0, ()], block(Expr(:global, name), Expr(:const, name),
        make_assignment(s, call(core(:_structtype), thismodule(), inert(name), call(core(:svec)), call(core(:svec), map(quotify, fields)))),
        make_assignment(outerref(name), s),
        call(core(:_setsuper!), name, super),
        call(core(:_typebody!), name, call(core(:svec), map(v -> core(:Box), fields))),
        Expr(:return, nothing)
    )))]
end

clear_capture_bits(vinfos::Dict) = map!(p -> set_capt!(p[2], false), vinfos)

function convert_lambda(lam::Expr, fname, interp, capt_sp)
    body = add_box_inits_to_body(lam, cl_convert(lam.args[3], fname, lam, Dict(), Dict(), false, interp))

    Expr(:lambda, lam_args(lam), [
        clear_capture_bits(lam_vinfo(lam).head),
        (),
        lam_vinfo(lam).args[2],
        union(lam_sp(lam), capt_sp)
        ], body)
end

# renumber ssavalues assigned in an expr, allowing it to be repeated
function renumber_assigned_ssavalues(e)
    vals = expr_find_all(x -> isassignment(x) && isssavalue(x.args[1]), e, x -> x.args[1].args[1])
    if isempty(vals)
        e
    else
        repl = Dict()
        foreach(id -> (repl[id] = make_ssavalue()), vals)
        function do_replace(x)
            if isatom(x) || isquoted(x)
                x
            else
                if x.head === :ssavalue
                    get(repl, x.args[1], false) || x
                else
                    Expr(x.head, map(do_replace, x.args)...)
                end
            end
        end
    end
end

function convert_for_type_decl(rhs, t)
    if t === core(:Any)
        rhs
    else
        temp = if isatom(t) || isssavalue(t) || isquoted(t)
            false
        else
            make_ssavalue()
        end
        ty = temp !== false ? temp : t
        ex = call(core(:typeassert), call(top(:convert), ty, rhs), ty)
        if temp !== false
            block(make_assignment(temp, renumber_assigned_ssavalues(t)), ex)
        else 
            ex
        end
    end
end

# convert assignment to a closed variable to a setfield! call.
# while we're at it, generate `convert` calls for variables with
# declared types.
# when doing this, the original value needs to be preserved, to
# ensure the expression `a=b` always returns exactly `b`.
function convert_assignment(var, rhs0, fname, lam, interp)
    if issymbol(var)
        vi = get(lam_vinfo(lam)[1], var, nothing)
        cv = get(lam_vinfo(lam)[2], var, nothing)
        vt = (vi !== nothing && vinfo_type(vi)) || (cv !== nothing && vinfo_type(cv)) || core(:Any)
        closed = cv !== nothing && vinfo_asgn(cv) && cinfo_capt(cv)
        capt = vi !== nothing && vinfo_asgn(vi) && cinfo_capt(vi)

        if !closed && !capt && vt == core(:Any)
            make_assignment(var, rhs0)
        else
            rhs1 = (issimple_atom(rhs0) || rhs0 == Expr(:the_exception)) ? rhs0 : make_ssavalue()
            rhs = vt == core(:Any) ? rhs1 : convert_for_type_decl(rhs1, cl_convert(vt, fname, lam, false, false, false, interp))
            ex = if closed 
                call(core(:setfield!), interp ? Expr(:$, var) : capt_var_access(var, fname, opaq), inert(:contents), rhs)
            elseif capt
                call(core(:setfield!), var, intert(:contents), rhs)
            else
                make_assignment(var, rhs)
            end
            if rhs1 == rhs0
                block(ex, rhs0)
            else
                block(make_assignment(rhs1, rhs0), ex, rhs1)
            end
        end
    elseif isouterref(var) || isglobalref(var)
        make_assignment(var, rhs0)
    elseif isssavalue(var)
        make_assignment(var, rhs0)
    else
        error("invalid assignment location \"$(deparse(var))\"")
    end
end

function rename_sig_types(ex, namemap)
    if ex isa Expr
        if ex.head == :call && length(ex.args) == 2 && 
            ex.args[1] isa Expr && ex.args[1].head === :core && ex.args[1].args[1] == :Typeof
            get(namemap, ex.args[2], ex)
        else
            ex1 = Expr(ex.head)
            for a in ex.args
                push!(ex1.args, rename_sig_types(a, namemap))
            end
            ex1
        end
    elseif ex isa Vector
        out = []
        for a in ex
            push!(out, rename_sig_types(a, namemap))
        end
        out
    else
        ex
    end
end

function fix_function_arg_type(te::Expr, typ, iskw, namemap, type_sp)
    typapp = te.args[2]
    types = rename_sig_types(typapp.args[2:end], namemap)
    closure_type = isempty(type_sp) ? typ : call(core(:apply_type), typ, type_sp...)
    newtypes = iskw ? Expr(types.head, types.args[1], closure_type, types.args[3:end]...) : d
    error()
end

function lift_toplevel(e)
    top = []
    function lift_(e)
        if isatom(e) || isquoted(e)
            e
        else
            e1 = Expr(e.head)
            for a in e.args
                push!(e1.args, lift_(a))
            end
            if e1.head == :var"toplevel-butfirst"
                push!(top, e1.args[2:end])
                e1.args[1]
            else
                e1
            end
        end
    end

    e2 = lift_(e)
    stmts = vcat(top...)
    structs, others = separate(x -> x isa Expr && x.head == :thunk, stmts)
    e2, [structs; others]
end


function add_box_inits_to_body(lam, body)
    vis = lam_vinfo(lam)[1]
    inits = Expr[]
    for arg in lam_args(lam)
        arg = arg_name(arg)
        vi = get(vis, arg, nothing)
        if vi !== nothing && vinfo_asgn(vi) && vinfo_capt(vi)
            push!(inits, make_assignment(arg, call(core(:Box), arg)))
        end
    end
    insert_after_meta(body, inits)
end

function all_methods_for(ex, body)
    mname = method_expr_name(ex)
    expr_find_all(x -> s isa Expr && length(s.args) > 1 && s.head === :method && method_expr_name(s) == mname,
        body,
        identity,
        x -> x isa Expr && x.head !== :lambda)
end

const lambda_opt_ignored_exprs = Set([:quote, :top, :core, :line, :inert, :var"local-def", :unnecessary, :copyast, :meta, :inbounds, :boundscheck, :loopinfo, :decl, :aliasscope, :popaliasscope, :thunk, :var"with-static-parameters", :var"toplevel-only", :global, :globalref, :outerref, :var"const-if-global", :thismodule, :const, :null, :true, :false, :ssavalue, :isdefined, :toplevel, :module, :lambda, :error, :gc_preserve_begin, :gc_preserve_end, :import, :using, :export])

islocal_in(s, lam) = haskey(lam_vinfo(lam)[1], s) || haskey(lam_vinfo(lam)[2], s)

# Try to identify never-undef variables, and then clear the `captured` flag for single-assigned,
# never-undef variables to avoid allocating unnecessary `Box`es.
function lambda_optimize_vars!(lam::Expr)
    @assert lam.head === :lambda

    all_methods_table = Dict()
    function get_methods(ex, stmts)
        mn = method_expr_name(ex)
        if haskey(all_methods_table, mn)
            all_methods_table[mn]
        else
            am = all_methods_for(ex, stmts)
            all_methods_table[mn] = am
            am
        end
    end

    vi = lam_vinfo(lam)[1]
    args = lam_argnames(lam)
    decl = Dict()
    unused = Dict()     # variables not (yet) used (read from) in the current block
    live = Dict()       # variables that have been set in the current block
    seen = Dict()       # all variables we've seen assignments to

    # Collect candidate variables: those that are captured (and hence we want to optimize)
    # and only assigned once. This populates the initial `unused` table.
    foreach(v -> capt(v) && sa(v) && (unused[v[1]] = true), vi)
    function restore(old)
        for (k,v) in live
            if !haskey(old, k)
                unused[k] = v
            end
        end
        # todo: must set `live = restore(old)` on call
        old
    end
    
    kill() = restore(Dict()) # when we see control flow, empty live set back into unused set

    mark_used(var) = haskey(unused, var) && !(var in args) && delete!(unused, var)
    
    mark_captured(var) = haskey(unused, var) && delete!(unused, var)

    function assign!(var)
        if haskey(unused, var)
            live[var] = true
            seen[var] = true
            delete!(unused, var)
        end
    end

    declare!(var) = haskey(unused, var) && (decl[var] = true)

    function leave_loop!(old_decls)
        foreach(k -> haskey(old_decls, k) && delete!(live, k), keys(live))
        # todo: all calls must follow `decl = leave_loop..`
        old_decls
    end

    function visit(e)
        if isatom(e)
            issymbol(e) && mark_used(e)
            false
        elseif lambda_opt_ignored_exprs(e.head)
            false
        elseif e.head in (:block, :call, :new, :splatnew)
            eager_any(visit, e.args)
        elseif e.head === :var"break-block"
            visit(e.args[2])
        elseif e.head === :return
            r = visit(e.args[1])
            kill() # todo: must alter var outside this scope
            r
        elseif e.head in (:break, :label, :symbolicgoto)
            kill() # todo: must alter var outside this scope
            false
        elseif e.head === :symboliclabel
            kill() # todo: must alter var outside this scope
            true
        elseif e.head in (:if, :elseif, :trycatch, :tryfinally)
            prev = deepcopy(live) # todo: probably need to pass live around to all functions
            if eager_any(function (e)
                r = visit(e)
                kill()
                r
            end, e.args)
                kill()
                true
            else
                restore(prev)
                false
            end
        elseif e.head in (:_while, :_do_while)
            prev = deepcopy(live)
            decl_ = deepcopy(decl)
            result = eager_any(visit, e.args)
            e.head === :_while && kill()
            leave_loop!(decl_)
            if result
                true
            else
                restore(prev)
                false
            end
        elseif e.head === :(=)
            r = visit(e.args[2])
            assign!(e.args[1])
            r
        elseif e.head === :local
            declare!(e.args[1])
            false
        elseif e.head === :method
            if length(e.args) > 1
                mn = method_expr_name(e)
                all_methods = islocal_in(mn, lam) ? get_methods(e, lam_body(lam)) : [e]
                foreach(ex -> foreach(mark_captured, map(first, lam_vinfo(ex.args[3])[1])), all_methods)
                assign!(e.args[1])
            else
                false
            end
        else
            eager_any(visit, e.args)
        end
    end
end

function eager_any(f, list)
    ret = false
    for el in list
        ret |= f(el)
    end
    ret
end

function is_var_boxed(v, lam)
    vi = get(first(lam_vinfo(lam)), v, nothing)
    vi !== nothing && asgn(vi) && capt(vi) && return true
    cv = get(lam_vinfo(lam)[2], v, nothing)
    cv !== nothing && asgn(cv) && capt(cv) && return true
    false
end

istoplevel_preserving(e) = e isa Expr && e.head in (:if, :elseif, :block, :trycatch, :tryfinally)

function map_cl_convert(exprs, fname, lam, namemap, defined, toplevel, interp)
    if toplevel
        map(function (x)
            tl = lift_toplevel(cl_convert(x, fname, lam, namemap, defined, toplevel && istoplevel_preserving(x), interp))
            length(tl) == 1 ? first(tl) : block(tl[2:end]... , first(tl))
        end, exprs)
    else
        map(x -> cl_convert(x, fname, lam, namemap, defined, false, interp), exprs)
    end
end

function cl_convert(e, fname, lam, namemap, defined, toplevel, interp)
    if !lam && !(e isa Expr && e.head in (:lambda, :method, :macro))
        if isatom(e)
            e
        else
            Expr(e.head, map_cl_convert(e.args, fname, lam, namemap, defined, toplevel, interp))
        end
    else
        if issymbol(e)
            function new_under_var(name)
                g = named_gensy(name)
                vi = make_var_info(g)
                vi.state[6] = true # 32
                push!(lam_vinfo(lam), vi)
                g
            end
            function get_box_contents(box, typ)
                # lower in an UndefVar check to a similarly named variable (ref #20016)
                # so that closure lowering Box introduction doesn't impact the error message
                # and the compiler is expected to fold away the extraneous null check
                access = issymbol(box) ? box : make_ssavalue()
                undeftest = call(core(:isdefined), access, inert(:contents))
                undefvar = new_under_var(e)
                undefcheck = Expr(:if, undeftest, nothing, block(Expr(:newvar, undefvar), undefvar))
                val = call(core(:getfield), access, inert(:contents))
                val = typ == core(:Any) ? val : call(core(:typeassert), val, cl_convert(typ, fname, lam, namemap, defined, toplevel, interp))

                block(
                    box == access ? [] : [make_assignment(access, box)],
                    undefcheck,
                    val)
            end
            vi = get(lam_vinfo(lam)[1], e, nothing)
            cv = get(lam_vinfo(lam)[2], e, nothing)
            if e == fname
                e
            elseif e in lam_sp(lam)
                e
            elseif cv !== nothing
                access = interp ? Expr(:$, call(core(:QuoteNode), e)) : call(core(:getfield), fname, inert(e))
                if asgn(cv) && capt(cv)
                    get_box_contents(access, vinfo_type(cv))
                else
                    access
                end
            elseif vi !== nothing
                if asgn(vi) && capt(vi)
                    get_box_contents(e, vinfo_type(vi))
                else
                    e
                end
            end
        elseif isatom(e)
            e
        else
            if (e isa Expr && e.head in (:quote, :top, :core, :globalref, :outerref, :thismodule, :line, :break, :inert, :module, :toplevel, :null, :var"true", :var"false", :meta)) || e isa Nothing || e isa Bool
                e
            elseif e.head === :var"toplevel-only"
                if e.args[1] == :struct
                    defined[e.args[2]] = true
                end
                e
            elseif e.head === :(=)
                var = e.args[1]
                rhs = cl_convert(e.args[2], fname, lam, namemap, defined, toplevel, interp)
                convert_assignment(var, rhs, fname, lam, interp)
            end
        end
    end
end