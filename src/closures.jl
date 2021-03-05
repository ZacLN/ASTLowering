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
function convert_assignment(var, rhs0, fname, lame, interp, opaq)
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
            rhs = vt == core(:Any) ? rhs1 : convert_for_type_decl(rhs1, cl_convert(vt, fname, lam, false, false, false, interp, opaq))
            ex = if closed 
                call(core(:setfield!), interp ? Expr(:$, var) : capt_var_access(var, fname, opaq), intert(:contents), rhs)
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

function first_non_meta(blk, i)
    for elt in blk
        if !(elt isa Expr && elt.head === :meta)
            return elt
        end
    end
    false
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
