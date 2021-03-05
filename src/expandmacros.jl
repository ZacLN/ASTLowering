function julia_expand_macroscope(e)
    e
    # julia_expand_macroscopes_(rename_symbolic_labels(julia_expand_quotes(e)))
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

function resolve_expansion_vars_with_new_env()
    
end
