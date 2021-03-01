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
# function conver_assignment(var, rhs0, fname, lam, interp)
#     if issymbol(var)
#         vi = 
#     end
# end