function find_assigned_vars(e, vars = [])
    if !(e isa Expr) || isquoted(e)
        ()
    else
        if e.head in (:lambda, :var"scope-block", :module, :toplevel)
            []
        elseif e.head === :method
            v = decl_var(method_expr_name(e))
            issymbol(v) && push!(vars, v)
            length(e.args) !== 1 && find_assigned_vars(e.args[2], vars)
        elseif e.head == :(=)
            v = decl_var(e.args[1])
            find_assigned_vars(e.args[2], vars)
            if isssavalue(v) || isglobalref(v) || isouterref(v) || isunderscore_symbol(v)
            else
                push!(vars, v)
            end
        else
            foreach(x->find_assigned_vars(x, vars), e.args)
        end
    end
    unique!(vars)
end

function find_decls(kind, e, vars = Symbol[])
    if !(e isa Expr) || isquoted(e)
    elseif e.head in (:lambda, :var"scope-block", :module, :toplevel)
    elseif e.head == kind && !isunderscore_symbol(e.args[1])
        push!(vars, decl_var(e.args[1]))
    else
        foreach(x -> find_decls(kind, x, vars), e.args)
    end
    vars
end

find_local_decls(e) = find_decls(:local, e)
find_local_def_decls(e) = find_decls(:var"local-def", e)
find_global_decls(e) = find_decls(:global, e)

function find_scope_decl(e, kind)
    expr_contains_p(
        x -> x isa Expr && x.head == kind && x,
        e,
        x -> !(x isa Expr && x.head in (:lambda, :var"scope-block", :module, :toplevel))
    )
end

function check_valid_name(e)
    isvalid_name(e) || error("invalid identifier name \"$e\"")
end

mutable struct Scope
    lam
    args::Vector
    locals::Vector
    globals::Vector
    sp::Vector
    renames::Dict
    prev
    soft::Bool
    hard::Bool
    implicit_globals::Vector
    warn_vars
end

make_scope(lam = false, args = [], locals = [], globals = [], sp = [], renames = Dict(), prev = false, soft = false, hard = false, implicit_globals = [], warn_vars = false) = Scope(lam, args, locals, globals, sp, renames, prev, soft, hard, implicit_globals, warn_vars)

function var_kind(var, scope, exclude_top_level_globals = false)
    if scope isa Scope
        if var in (scope.args)
            :argument
        elseif var in scope.locals
            :local
        elseif var in scope.globals
            if exclude_top_level_globals && 
                isempty(lam_args(scope.lam)) &&
                (scope.prev === nothing || scope.prev.prev === nothing)
                :none            
            else
                :global
            end
        elseif var in scope.sp
            :var"static-parameter"
        else
            var_kind(var, scope.prev, exclude_top_level_globals)
        end
    else
        :none
    end
end

isin_scope(var, scope) = var_kind(var, scope) !== :none


remwarn_var(v, scope) = false
function remwarn_var(v, scope::Scope)
    w = scope.warn_vars
    if w isa Vector && (i = findfirst(w, v)) !== nothing
        deleteat!(w, i)
        true
    else
        remwarn_var(v, scope.prev)
    end
    false
end

all_local_names(scope, allnames = []) = allnames
function all_local_names(scope::Scope, allnames = [])
    append!(allnames, scope.args, scope.sp, scope.locals)
    all_local_names(scope.prev, allnames)
    allnames
end

resolve_scopes(e) = resolve_scopes_(e, false)

function resolve_scopes_(e, scope, sp = [], loc = false)
    if issymbol(e)
        lookup(scope, e)
    elseif !(e isa Expr) || isquoted(e) || e.head in (:toplevel, :symbolicgoto, :symboliclabel)
        e
    elseif e.head === :global
        check_valid_name(e.args[1])
        e
    elseif e.head in (:local, :var"local-def")
        check_valid_name(e.args[1])
        nothing
    elseif e.head === :var"require-existing-local"
        if !(isin_scope(e.args[2], scope))
            error("no outer local variable declaration exists for \"for outer\"")
        end
        nothing
    elseif e.head in (:softscope, :hardscope)
        nothing
    elseif e.head === :locals
        resolve_scopes_locals(e, scope, sp, loc)
    elseif e.head === :islocal
        !(var_kind(e.args[1], scope) in (:global, :none))
    elseif e.head === :lambda
        args = lam_argnames(e)
        body = resolve_scopes_(lam_body(e), make_scope(e, args, [], [], sp, Dict(), scope))
        Expr(:lambda, e.args[1], e.args[2], body)
    elseif e.head === :var"scope-block"
        resolve_scopes_scope_block(e, scope, sp, loc)
    elseif e.head === :module
        error("module expression not at top level")
    elseif e.head === :var"break-block"
        Expr(:var"break-block", e.args[1], resolve_scopes_(e.args[2], scope, [], loc))
    elseif e.head === :var"with-static-parameters"
        Expr(:var"with-static-parameters", resolve_scopes_(e.args[1], scope, e.args[2:end], loc), e.args[2:end]...)
    elseif e.head === :method && length(e.args) > 1
        Expr(:method,
            resolve_scopes_(e.args[1], scope),
            resolve_scopes_(e.args[2], scope),
            resolve_scopes_(e.args[3], scope, method_expr_static_parameters(e))
        )
    else
        if e.head === :(=) && issymbol(e.args[1]) && scope isa Scope && isempty(lam_args(scope.lam)) && remwarn_var(e.args[1], scope) && scopewarn_opt == 1
            v = e.args[1]
            loc = extract_line_file(loc)
            line = loc[1] == 0 ? julia_current_line : loc[1]
            file = loc[2] == :none ? julia_current_file : loc[2]
            lowering_warning(1000, :warn, Symbol(file, line), file, line, "Assignment to $v in soft scope is ambiguous because a global variable by the same name exists: $v will be treated as a new local. Disambiguate by using `local $v` to suppress this warning or `global $v` to assign to the existing global variable.")
        end
        ex = Expr(e.head)
        sizehint!(ex.args, length(e.args))
        for x in e.args
            if islinenum(x)
                loc = x 
            end
            resolve_scopes_(x, scope, [], loc)
            push!(ex.args, resolve_scopes_(x, scope, [], loc))
        end
        ex
    end
end

function resolve_scopes_locals(e, scope, sp, loc)
    names = filter!(v -> !isgensym(v) && length(split(string(v), "#")) == 2, all_local_names(scope))
    names = unique!(filter!(v -> isempty(string(v)), map(unmangled_name, names)))
    d = make_ssavalue()
    block(
        make_assignment(d, call(call(core(:apply_type), top(:Dict), core(:Symbol), core(:Any)))),
        map(v -> (var = resolve_scopes_(v, scope); Expr(:if, Expr(:isdefined, var), call(top(:setindex!), d, var, Expr(:quote,v)))), names)...,
        d
    )
end

function resolve_scopes_scope_block(e::Expr, scope, sp, loc)
    blok = e.args[1]
    lam = scope.lam
    argnames = lam_argnames(lam)
    istoplevel = isempty(argnames) && e == lam_body(lam)
    current_locals = lam.args[2]
    globals = find_global_decls(blok)
    assigned = find_assigned_vars(blok)
    locals_def = find_local_def_decls(blok)
    local_decls = find_local_decls(blok)
    hard = isempty(argnames) && (scope.hard || find_scope_decl(blok, :hardscope))
    soft = isempty(argnames) && !hard && let ss = find_scope_decl(blok, :softscope)
        if ss == false
            scope.soft
        elseif ss.args[1] == true
            true
        elseif ss.args[1] == false
            false
        else
            scope.soft
        end
    end
    nonloc_assigned = filter(v -> !(v in locals_def) && !(v in local_decls), assigned)
    implicit_globals = istoplevel ? nonloc_assigned : []
    implicit_locals = istoplevel ? [] : filter(v -> var_kind(v, scope, true) in (:none, :var"static-parameter") && !(soft && (v in scope.implicit_globals || defined_julia_global(v))) && !(v in globals) ,nonloc_assigned)
    locals_nondef = unique!(vcat(local_decls, implicit_locals))
    needs_rename = vars -> filter(v -> v in current_locals || isin_scope(v, scope),vars)
    need_rename = needs_rename(locals_nondef)
    need_rename_def = needs_rename(locals_def)
    renamed = map(named_gensy, need_rename)
    renamed_def = map(named_gensy, need_rename_def)
    newnames = vcat(setdiff(locals_nondef, need_rename), renamed)
    new_names_def = vcat(setdiff(locals_def, need_rename_def), renamed_def)
    warn_vars = !istoplevel && isempty(argnames) && !soft && !hard && let
        vars = filter(v -> (v in scope.implicit_globals || defined_julia_global(v)) && var_kind(v, scope) == :none && !(v in globals), nonloc_assigned)
        if !isempty(vars)
            Dict(v => true for v in vars)
        else
            false
        end
    end
    
    foreach(globals) do v
        if v in locals_def || v in local_decls
            error("variable \"$v\" declared both local and global")
        end
        if isempty(argnames) && var_kind(v, scope) in (:argument, :local)
            error("`global \"$v\"`: $v is a local variable in its enclosing scope")
        end
    end

    if !isempty(argnames) && e == lam_body(lam)
        foreach(local_decls) do v
            if v in argnames
                error("local variable name \"$v\" conflicts with an argument")
            end
        end
    end
    for list in (local_decls, implicit_locals)
        foreach(list) do v
            if var_kind(v, scope) == :var"static-parameter"
                error("local variable name \"$v\" conflicts with a static parameter")
            end
        end
    end

    if lam isa Expr
        lam.args[3] = vcat(lam.args[3], newnames, new_names_def)
        #todo : structure of lam not clear
    end

    renames = Dict()
    for i = 1:length(need_rename)
        renames[need_rename[i]] = renamed[i]
    end
    for i = 1:length(need_rename_def)
        renames[need_rename_def[i]] = renamed_def[i]
    end
    insert_after_meta(blockify(resolve_scopes_(blok, 
        make_scope(
            lam,
            [],
            vcat(locals_nondef, locals_def),
            globals,
            [],
            renames,
            scope,
            soft && isempty(argnames),
            hard,
            istoplevel ? implicit_globals : scope.implicit_globals,
            warn_vars
        ), [], loc)),
    vcat(map(v -> Expr(:local, v), newnames), map(local_def, new_names_def)))
end


function lookup(scope, e)
    if scope isa Scope
        if e in scope.args
            e
        elseif e in scope.globals
            outerref(e)
        else
            r = get(scope.renames, e, nothing)
            if r !== nothing
                r
            elseif e in scope.locals
                e
            elseif e in scope.sp
                e
            else
                lookup(scope.prev, e)
            end

        end
    else
        if isunderscore_symbol(e)
            e
        else
            outerref(e)
        end
    end
end