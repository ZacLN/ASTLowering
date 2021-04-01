mutable struct VarInfo
    name::Symbol
    type
    state::BitVector
end

var_info_for(key, env::Dict{Any,VarInfo}) = get(env, key, false)
make_var_info(name) = VarInfo(name, core(:Any), BitVector(undef, 8))

vinfo_name(v::VarInfo) = v.name
vinfo_type(v::VarInfo) = v.type

set_type!(v::VarInfo, t) = (v.type = t)

capt(v::VarInfo) = v.state[1]
asgn(v::VarInfo) = v.state[2]
neverundef(v::VarInfo) = v.state[3]
read(v::VarInfo) = v.state[4]
sa(v::VarInfo) = v.state[5]

set_capt!(v::VarInfo, a) = (v.state[1] = a)
set_asgn!(v::VarInfo, a) = (v.state[2] = a)
set_neverundef!(v::VarInfo, a) = (v.state[3] = a)
set_read!(v::VarInfo, a) = (v.state[4] = a)
set_sa!(v::VarInfo, a) = (v.state[5] = a)
set_called!(v::VarInfo, a) = (v.state[7] = a)

function lambda_all_vars(e::Expr)
    vcat(lam_argnames(e), e.args[2])
end

function free_vars(e, tab::Set{Symbol} = Set{Symbol}())
    if e == UNUSED || isunderscore_symbol(e)
        tab
    elseif issymbol(e)
        push!(tab, e)
        tab
    elseif isouterref(e)
        tab
    elseif e isa Expr && e.head == :var"break-block"
        free_vars(e.args[2], tab)
    elseif e isa Expr && e.head == :var"with-static-parameters"
        free_vars(e.args[2], tab)
    elseif isatom(e) || isquoted(e)
        tab
    elseif e.head === :lambda
        bound = lambda_all_vars(e)
        foreach(v -> !(v in bound) && push!(tab, v), free_vars(lam_body(e)))
        tab
    elseif e isa Expr
        foreach(x -> free_vars(x, tab), e.args)
        tab
    elseif e isa Vector
        foreach(x -> free_vars(x, tab), e.args)
        tab
    else 
        error()
    end
end

function analyze_vars_lambda(e::Expr, env::Dict{Any,VarInfo}, captvars::Dict{Any,VarInfo}, sp, new_sp, methsig = false)
    args = lam_args(e)
    locl = e.args[2]
    allv = vcat(map(arg_name, args), locl)
    fv = let fv = setdiff(free_vars(lam_body(e)), allv)
        dv = vcat(map(v -> let vi = var_info_for(v, env)
            if vi !== false
                free_vars(vinfo_type(vi))
            else 
                []
            end
        end, collect(fv))...)
    end
    sig_fv = methsig !== false ? free_vars(methsig) : ()
    glo = find_global_decls(lam_body(e))
    vi = Dict{Any,VarInfo}()
    for decl in args
        vi[decl] = make_var_info(decl)
    end
    for decl in locl
        vi[decl] = make_var_info(decl)
    end
    capt_sp::Vector = filter(v -> (v in fv && !(v in glo)) || !(v in new_sp) || v in sig_fv, sp)
    
    cv::Dict{Any,VarInfo} = merge(filter(v -> vinfo_name(v[2]) in fv && !(vinfo_name(v[2]) in new_sp) && !(vinfo_name(v[2]) in glo), env), Dict{Any,VarInfo}(a => make_var_info(a) for a in capt_sp))
    
    
    analyze_vars(lam_body(e), merge(vi, filter(v -> !(vinfo_name(v[2]) in allv) && !(vinfo_name(v[2]) in glo), env)), cv, union(new_sp, sp))
    foreach(v -> set_capt!(v, true), cv)
    e.args[2] = [vi, cv, 0, union(new_sp, capt_sp)]
    e
end

function analyze_vars(e, env::Dict{Any,VarInfo}, captvars::Dict{Any,VarInfo}, sp)
    if isatom(e) || isquoted(e)
        if issymbol(e)
            vi = var_info_for(e, env)
            if vi !== false
                set_read!(vi, true)
            end
        end
        e
    else
        if e.head == :var"local-def"
            # a local that we know has an assignment that dominates all usages
            vi = var_info_for(e.args[1], env)
            set_neverundef!(vi, true)
        elseif e.head == :(=)
            vi = issymbol(e.args[1]) && var_info_for(e.args[1], env)
            if vi !== false
                if asgn(vi)
                    set_sa!(vi, false)
                else
                    set_sa!(vi, true)
                end
                set_asgn!(vi, true)
            else
                analyze_vars(e.args[2], env, captvars, sp)
            end
        elseif e.head === :call
            vi = var_info_for(e.args[1], env)
            if vi !== false
                set_called!(vi, true)
            end
            foreach(x -> analyze_vars(x, env, captvars, sp), e.args[2:end])
        elseif e.head == :decl
            vi = var_info_for(e.args[1], env)
            if vi !== false
                if vinfo_type(vi) !== core(:Any)
                    error("multiple type declarations for \"$(e.args[1])\"")
                end
                if haskey(captvars, e.args[1])
                    error("type of \"$(e.args[1])\" declared in inner scope")
                end
                set_type!(vi, e.args[2])
            end
        elseif e.head === :lambda
            analyze_vars_lambda(e, env, captvars, sp, [])
        elseif e.head === :var"with-static-parameters"
            @assert e.args[1].head === :lambda
            analyze_vars_lambda(e.args[1], env, captvars, sp, e.args[2:end])
        elseif e.head === :method
            if length(e.args) == 1
                vi = var_info_for(method_expr_name(e), env)
                if vi !== false
                    if asgn(vi)
                        set_sa!(vi, false)
                    else
                        set_sa!(vi, true)
                    end
                    set_asgn!(vi, true)
                end
                e
            else
                analyze_vars(e.args[2], env, captvars, sp)
                @assert e.args[3].head === :lambda
                analyze_vars_lambda(e.args[3], env, captvars, sp, method_expr_static_parameters(e), e.args[2])
            end
        elseif e.head in (:module, :toplevel)
            e
        else
            foreach(x -> analyze_vars(x, env, captvars, sp), e.args)
        end
    end
end

function analyze_variables!(e)
    analyze_vars(e, Dict{Any,VarInfo}(), Dict{Any,VarInfo}(), [])
    e
end

