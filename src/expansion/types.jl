function expand_abstract(e)
    sig = e.args[1]
    name, params, super = analyze_type_sig(sig)
    expand_forms(abstract_type_def_expr(name, params, super))
end

function abstract_type_def_expr(name, params, super)
    params, bounds = sparam_name_bounds(params)
    block(
        Expr(:global, name), Expr(:const, name),
        Expr(:var"scope-block",
        block(
            local_def(name),
            map(v -> Expr(:local, v), params)...,
            map((n,v) -> make_assignment(n, bounds_to_TypeVar(v, true)), params, bounds)...,
            Expr(:var"toplevel-only", :abstract_type),
            make_assignment(name, call(core(:_abstracttype), (:thismodule), inert(name), call(core(:svec), params...))),
            call(core(:_setsuper!), name, super),
            call(core(:_typebody!), name),
            Expr(:if, Expr(:&&, Expr(:isdefined, outerref(name)), call(core(:_equiv_typedef), outerref(name), name)),
                :null,
                make_assignment(outerref(name), name)),
            :null)))
end

function expand_primitive(e)
    sig = e.args[1]
    n = e.args[2]
    name, params, super = analyze_type_sig(sig)
    expand_forms(primitive_type_def_expr(n, name, params, super))
end

function primitive_type_def_expr(n, name, params, super)
    params, bounds = sparam_name_bounds(params)
    block(
        Expr(:global, name), Expr(:const, name),
        Expr(:var"scope-block",
        block(
            local_def(name),
            map(v -> Expr(:local, v), params)...,
            map((n,v) -> make_assignment(n, bounds_to_TypeVar(v, true)), params, bounds)...,
            Expr(:var"toplevel-only", :primitive_type),
            Expr(:(=), name, call(core(:_primitivetype), (:thismodule), inert(name), call(core(:svec), params...), n)),
            call(core(:_setsuper!), name, super),
            call(core(:_typebody!), name),
            Expr(:if, Expr(:&&, Expr(:isdefined, outerref(name)), (call(core(:_equiv_typedef), outerref(name), name))),
                nothing,
                Expr(:(=), outerref(name), name)),
            nothing)))
end


function expand_struct_def(e)
    mut = e.args[1]
    sig = e.args[2]
    fields = e.args[3].args
    for x in fields
        if issymbol(x) || isdecl(x) || islinenum(x)
        elseif isassignment(x) && (issymbol(x.args[1]) || isdecl(x.args[1]))
            error("$(deparse(x)) inside type definition is reserved")
        end
    end
    name, params, super = analyze_type_sig(sig)
    ex = struct_def_expr(name, params, super, fields, mut)
    expand_forms(ex)
end

function struct_def_expr(name, params, super, fields, mut)
    params, bounds = sparam_name_bounds(params)
    struct_def_expr_(name, params, bounds, super, flatten_blocks(fields), mut)
end

function struct_def_expr_(name, params::Vector, bounds, super, fields0, mut)
    fields, defs = separate(x -> issymbol(x) || isdecl(x), fields0)
    defs = filter!(x -> !iseffect_free(x), defs)
    locs = length(fields0) > 0 && islinenum(fields0[1]) ? [fields0[1]] : []
    field_names = map(decl_var, fields)
    field_types = map(decl_type, fields)
    defs2 = isempty(defs) ? default_inner_ctors(name, field_names, field_types, params, bounds, locs) : defs
    min_initialized = min(ctors_min_initialized(defs), length(fields))
    prev = make_ssavalue()
    
    has_dups(field_names) && error("duplicate field name")
    map(v -> !issymbol(v) && error("field name $v is not a symbol"), field_names)
    
    block(
        Expr(:global, name), Expr(:const, name),
        Expr(:var"scope-block",
            block( 
                :hardscope,
                local_def(name),
                map(v -> Expr(:local, v), params)...,
                map((n,v) -> make_assignment(n, bounds_to_TypeVar(v, true)), params, bounds)...,
                Expr(:var"toplevel-only", :struct, outerref(name)),
                make_assignment(name, call(core(:_structtype), (:thismodule), inert( name), call(core(:svec), params...), 
                    call(core(:svec), map(quotify, field_names)...), 
                    mut, min_initialized)),
                call(core(:_setsuper!), name, super),
                Expr(:if, Expr(:isdefined, Expr(:outerref, name)),
                    block(
                        make_assignment(prev, outerref(name)),
                        Expr(:if, call(core(:_equiv_typedef), prev, name),
                            block(make_assignment(name, prev),
                                (if ispair(params)
                                    [make_assignment(Expr(:tuple, params...), Expr(:., foldl((_,x) -> Expr(:., x, Expr(:quote, :body)), params, init = prev), Expr(:quote, :parameters)))]
                                else
                                    []
                                end)...),
                            make_assignment(outerref(name), name))),
                    make_assignment(outerref(name), name)),
                call(core(:_typebody!), name, call(core(:svec), field_types...)), :null)),
        # inner constructors
        Expr(:var"scope-block",
            block(
                :hardscope,
                Expr(:global, name),
                map(c -> rewrite_ctor(c, name, params, field_names, field_types), defs2)...)),
        # outer constructors
        (if isempty(defs) && !isempty(params)
            [Expr(:var"scope-block",
                block(
                    Expr(:global, name),
                    default_outer_ctor(name, field_names, field_types, params, bounds, locs)))]
        else
            []
        end)...,
    :null
    )
end

function check_params_occured(root_types::Vector, sp::Vector, i)
    if i > length(sp)
        true
    else
        p = sp[i]
        push!(root_types, p[2:end])
        expr_contains_eq(p[1], Expr(:list, root_types)) && check_params_occured(root_types, sp, i + 1)
    end
end

function rewrite_ctor(ctor, Tname, params, field_names, field_types)
    function ctor_body(x, type_params, sparams)
        if x isa Expr && x.head === :call && length(x.args) > 0
            if x.args[1] == :new
                args = []
                for i = 2:length(x.args)
                    push!(args, ctor_body(x.args[i], type_params, sparams))
                end
                return new_call(Tname, type_params, sparams, params, args, field_names, field_types)
            elseif x.args[1] isa Expr && x.args[1].head == :curly && x.args[1].args[1] == :new
                p, args = [], []
                for i = 2:length(x.args[1].args)
                    push!(p, x.args[1].args)
                end
                for i = 2:length(x.args)
                    push!(args, ctor_body(x.args[i], type_params, sparams))
                end
                return new_call(Tname, p, sparams, params, args, field_names, field_types)
            end
        end
        if x isa Expr
            ex =  Expr(x.head)
            for a in x.args
                push!(ex.args, ctor_body(a, type_params, sparams))
            end
            return ex
        else
            return x
        end
    end
    rewrite_ctor_(flatten_all_where_expr(ctor), Tname, ctor_body)
end

function rewrite_ctor_(x, Tname, ctor_body)
    if x isa Expr && (x.head === :function || x.head == :(=)) && length(x.args) == 2 && x.args[1] isa Expr && x.args[2] isa Expr
        sig = x.args[1]
        wheres = []
        if sig.head == :where
            for i = 2:length(sig.args)
                push!(wheres, sig.args[i])
            end
            sig = sig.args[1]
        end
        if sig isa Expr && sig.head == :(::)
            sig = sig.args[1]
        end
        if sig isa Expr && sig.head == :call && length(sig.args) > 0
            name = sig.args[1]
            sig = sig.args[2:end]
            body = x.args[2]
            return ctor_def(name, Tname, ctor_body, sig, body, wheres)
        end
        sig = x.args[1]
    end

    if x isa Expr
        ex = Expr(x.head)
        for a in x.args
            push!(ex.args, rewrite_ctor_(a, Tname, ctor_body))
        end
        ex
    else
        x
    end
end


function default_inner_ctors(name, field_names, field_types, params, bounds, locs)
    field_names = safe_field_names(field_names, field_types)
    any_ctor = Expr(:function,
        with_wheres(call(isempty(params) ? name : Expr(:curly, name, params...), field_names...), 
            map(b -> Expr(:var"var-bounds", b), bounds)),
        block(locs..., 
            call(:new, field_names...))
        )

    if isempty(params) && any(t -> t != Expr(:core, :Any), field_types) 
        [Expr(:if, 
            foldl((a,b) -> Expr(:&&, a, b), map(t -> call(core(:(===)), core(:Any), t), field_types)),
            block(), Expr(:function, call(name, map(make_decl, field_names, field_types)...), block(locs..., Expr(:new, Expr(:outerref, name), field_names...)))),
            any_ctor
        ]
    else
        [any_ctor]
    end
end


function default_outer_ctor(name, field_names, field_types, params, bounds, locs)
    field_names = safe_field_names(field_names, field_types)
    Expr(:function, with_wheres(call(name, map(make_decl, field_names, field_types)...), map(b -> Expr(:var"var-bounds", b), bounds)),
        block(locs..., call(Expr(:curly, name, params...), field_names...)))
end


function ctor_def(name, Tname, ctor_body, sig, body, wheres)
    iscurly = name isa Expr && name.head === :curly
    curlyargs = iscurly ? name.args[2:end] : []
    name = iscurly ? name.args[1] : name
    sparams = map(first, map(analyze_typevar, wheres))
    if name != Tname
        Expr(:function, with_wheres(call(iscurly ? Expr(:curly, name, curlyargs...) : name, sig...), wheres),
            ctor_body(body, [], sparams))
    else
        Expr(:function, with_wheres(call(iscurly ? Expr(:curly, name, curlyargs...) : name, sig...), wheres),
            ctor_body(body, curlyargs, sparams))
    end
end

function ctors_min_initialized(defs)
    n = typemax(Int)
    for expr in defs
        x = expr_contains_p(x -> x isa Expr && x.head == :call && x.args[1] == :new && x, expr)
        if x isa Expr
            n = min(length(x.args) - 1, n)
        end
    end
    n
end


function analyze_type_sig(ex, params = [], super = nothing)
    if ex isa Symbol
        name = ex
    elseif iscurly(ex) && isempty(params)
        for i in 2:length(ex.args) 
            push!(params, ex.args[i])
        end
        return analyze_type_sig(ex.args[1], params, super)
    elseif super === nothing && ex.head == :<:
        super = ex.args[2]
        return analyze_type_sig(ex.args[1], params, super)
    else
        error("invalid type signature")
    end
    return name, params, something(super, core(:Any))
end


function new_call(Tname, type_params, sparams, params, args, field_names, field_types)
    any(iskwarg, args) && error("new does not accept keyword argumetns")
    let nnv = num_non_varargs(type_params)
        !any(isvararg, type_params) && length(params) > nnv && error("too few type parameters specified in new{...}")
        nnv > length(params) && error("too many type parameters specified in new{...}")
    end
    Texpr = isempty(type_params) ? outerref(Tname) : Expr(:curly, outerref(Tname), type_params...)
    tn = make_ssavalue()
    field_convert = function (fld, fty, val)
        if fty == core(:Any)
            val
        else
            call(top(:convert), type_params == params && fty in params && fty in sparams ? fty : call(core(:fieldtype), tn, fld), val) 
        end
    end
    
    if num_non_varargs(args) > length(field_names)
        call(core(:throw), call(top(:ArgumentError), "new: too many arguments (expected $(length(field_names)))"))
    elseif any(isvararg, args)
        if all(==(core(:Any)), field_types)
            Expr(:splantnew, Texpr, call(core(:tuple), args...))
        else
            argt = make_ssavalue()
            nf = make_ssavalue()
            Expr(:block,
            make_assignment(tn, Texpr),
            make_assignment(argt, call(core(:tuple), args...)),
            make_assignment(nf, call(core(:nfields), argt)),
            Expr(:if, call(top(:ult_int), nf, length(field_names)), call(core(:throw), call(top(:ArgumentError), "new: too few arguments (expected $(length(field_names)))"))),
            Expr(:if, call(top(:ult_int), length(field_names), nf), call(core(:throw), call(top(:ArgumentError), "new: too many arguments (expected $(length(field_names)))"))),
            Expr(:new, tn, map((fld, fty) -> field_convert(fld, fty, call(core(:getfield), argt, fld, false)), 1:length(field_names), field_types[1:length(field_names)]))
            )
        end
    else
        block(
            make_assignment(tn, Texpr),
            Expr(:new, tn, map(field_convert, 1:length(args), field_types[1:length(args)], args)...)
        )
    end
end



function safe_field_names(field_names, field_types)
    if any(v -> contains(e -> e == v, field_types), field_names)
        map(x -> gensy(), field_names)
    else
        map(x -> x == :_ ? gensy() : x, field_names)
    end
end

function with_wheres(call, wheres)
    if !isempty(wheres)
        Expr(:where, call, wheres...)
    else
        call
    end
end

function sparam_name_bounds(params)
    bounds = map(analyze_typevar, params)
    map(first, bounds), bounds
end
