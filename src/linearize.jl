function linearize(e)
    if !(e isa Expr) || isquoted(e)
        e
    elseif e.head === :lambda
        e.args[4:end] = compile_body(e.args[3], e.args[2][1:2], e)
    else
        e1 = Expr(e.head)
        for a in e.args
            push!(e1.args, linearize(a))
        end
        e = e1
    end
    e
end

isvalid_ir_argument(e) = issimple_atom(e) || issymbol(e) || (e isa Expr && e.head in (:quote, :inert, :top, :core, :globalref, :outerref, :slot, :static_parameter, :boundscheck))

isvalid_ir_value(lhs, e) = isssavalue(lhs) || 
                           isvalid_ir_argument(e) ||
                           (issymbol(lhs) && e isa Expr && e.head in (:new, :splatnew, :the_expection, :isdefined, :call, :invoke, :foreigncall, :cfunction, :gc_preserve_begin, :copyast, :new_opaque_closure))

isvalid_ir_return(e) = isvalid_ir_argument(e) || (e isa Expr && e.head === :lambda

# this pass behaves like an interpreter on the given code.
# to perform stateful operations, it calls `emit` to record that something
# needs to be done. in value position, it returns an expression computing
# the needed value. in the future, all intermediate values will have
# numbered slots (or be simple immediate values), and then those will be the
# only possible returned values.
function compile_body(e, vi, lam)
    code = [] # statements
    filename = true
    first_line = false
    current_loc = false
    rett = false
    global_const_error = false
    arg_map = false             # map arguments to new names if they are assigned
    label_counter = 0           # counter for generating label addresses
    label_map = Dict()          # maps label names to generated addresses
    label_nesting = Dict()      # exception handler and catch block nesting of each label
    finally_handler = false     # Current finally block info: `(var label map level tokens)` 
                                # `map` is a list of `(tag . action)` which will
                                # be emitted at the exit of the block. Code
                                # should enter the finally block via `enter-finally-block`.
    handler_goto_fixups = []    # `goto`s that might need `leave` exprs added
    handler_level = 0           # exception handler nesting depth
    catch_token_stack = []      # tokens identifying handler enter for current catch blocks
    
    function emit(c)
        push!(code, c)
        c
    end
    
    function make_label()
        label_counter += 1
        label_counter - 1
    end
    
    mark_label(l) = emit(Expr(:label, l))
    
    function make_and_mark_label()
        if !isempty(code) && last(code) isa Expr && last(code).head == :label
            last(code).args[1]
        else
            l = make_label()
            mark_label(l)
            l # todo : is this right?
        end
    end
    
    function enter_finally_block(action, need_goto = true)
        tags = finally_handler[3]
        tag = isempty(tags) ? 1 : first(last(tags)) + 1
        push!(tags, tag)
        emit(make_assignment(first(finally_handler), tag))
        if need_goto
            label = finally_handler[2]
            dest_handler_level = finally_handler[4]
            dest_tokens = finally_handler[5]
            pexc = pop_exc_expr(catch_token_stack, dest_tokens)
            pexc !== false && emit(pexc)
            emit(Expr(:leave, 1 + (handler_level - dest_handler_level)))
            emit(Expr(:goto, label))
        end
        tag
    end

    function pop_exc_expr(src_tokens, dest_tokens)
        if src_tokens == dest_tokens
            false
        else
            for i in 1:length(src_tokens)
                if length(src_tokens) - i == length(dest_tokens) && src_tokens[i + 1:end] == dest_tokens
                    return Expr(:pop_exception, src_tokens[i]) 
                end
            end
            error("Attempt to jump into catch block")
        end
    end

    function emit_return(x)
        function actually_return(x)
            x = if rett
                compile(convert_for_type_decl(x, rett), [],. true, false)
            else
                x
            end
            tmp = if (isempty(catch_token_stack) ? isvalid_ir_return : issimple_atom)(x)
                false
            else
                make_ssavalue()
            end
            tmp !== false && emit(make_assignment(tmp, x))
            pexc = pop_exc_expr(catch_token_stack, [])
            pexc !== false && emit(pexc)
            emit(Expr(:return, tmp !== false ? tmp : x))

        end

        if x
            if handler_level > 0
                tmp = if issimple_atom(x) && (!isssavalue(x) || finally_handler == false)
                    false
                elseif finally_handler !== false 
                    new_mutable_var()
                else
                    make_ssavalue()
                end
                tmp !== false && emit(make_assignment(tmp, x))
                if finally_handler !== false
                    enter_finally_block(Expr(:return, tmp !== false ? tmp : x))
                else
                    emit(Expr(:leave, handler_level))
                    actually_return(tmp !== false ? tmp : x)
                end
                tmp !== false ? tmp : x
            else
                actually_return(x)
            end
        else
            false # todo : correct?
        end
    end

    function emit_break(labl) # todo : check type?
        lvl = labl.args[2]
        dest_tokens = labl.args[3]
        if finally_handler !== false && finally_handler[4] > lvl
            enter_finally_block(Expr(:break, labl))
        else
            pexc = pop_exc_expr(catch_token_stack, dest_tokens)
            pexc !== nothing && emit(pexc)
            if handler_level > lvl
                emit(Expr(:leave, handler_level - lvl))
            end
            emit(Expr(:goto, labl.args[1]))
        end
    end

    function new_mutable_var(name...)
        g = isempty(name) ? gensy() : named_gensy(first(name))
        push!(lam_vinfo(lam)[1], VarInfo(g, :Any, BitArray((false, true, false, false, false, false, false, false)))) 
        g
    end

    function check_top_level(e)
        function head_to_text(h)
            if h == :abstract_type 
                "\"abstract type\""
            elseif h === :primitive_type
                "\"primitive type\""
            elseif h === :struct_type
                "\"struct\""
            elseif h === :method
                "\"method definition\""
            else
                string("\"$h\"")
            end
        end
        if !isempty(lam[2]) # todo: use lam accessor func
            error("$(head_to_text(h)) expression not at top level")
        end
    end

    function compile_args(lst, break_labels)
        issimple = all(x -> issimple_atom(x) || issymbol(x) || (x isa Expr && x.head in (:quote, :inert, :top, :core, :globalref, :outerref, :boundscheck)), lst)

        vals = []
        for arg in lst
            aval = compile(arg, break_labels, true, false)
            aval = aval == false ? nothing : aval
            push!(vals, if !issimple &&
                           !issimple_atom(arg) &&
                           !issimple_atom(aval) &&
                           !(arg isa Expr && arg.head in (:quote, :inert, :top, :core, :globalref, :outerref, :boundscheck)) &&
                           !(issymbol(aval) && aval in lam_args(lam)) &&
                           !(issymbol(arg) && (arg == last(lst) || isempty(vals)))
                tmp = make_ssavalue()
                emit(make_assignment(tmp, aval))
                tmp
            else
                aval
            end)
        end
        vals
    end

    function compile_cond(ex, break_labels)
        cnd = compile(ex, break_labels, true, false)
        cnd = cnd == false ? nothing : cnd
        if !isvalid_ir_argument(cnd)
            tmp = make_ssavalue()
            emit(make_assignment(tmp, cnd))
            tmp
        else
            cnd
        end
    end
    
    function emit_assignment(lhs, rhs)
        if rhs
            if isvalid_ir_value(lhs, rhs)
                emit(make_assignment(lhs, rhs))
            else
                rr = make_ssavalue()
                emit(make_assignment(rr, rhs))
                emit(make_assignment(lhs, rr))
            end
        else
            false
        end
    end

    function compile(e, break_labels, value::Bool, tail::Bool)
        if !(e isa Expr || e.head in (:null, :true, :false, :ssavalue, :quote, :inert, :top, :core, :copyast, :the_expection, :$, :globalref, :outerref, :thismodule, :cdecl, :stdcall, :fastcall, :thiscall, :llvmcall))
            e1 = get(argmap, e, e)
            if value || isunderscore_symbol(e) || (e isa Expr && (e.head == :outerref || e.head == :globalref) && isunderscore_symbol(e.args[1]))
                error("all-underscore identifier used as rvalue $(format_loc(current_loc))")
            end

            if tail
                emit_return(e1)
            elseif value
                e1
            elseif issymbol(e1)
                emit(e1)
                false
            elseif e1 isa Expr && e1.head == :outerref
                emit(e1)
                false
            elseif e1 isa Expr && e1.head == :globalref
                emit(e1)
                false
            else
                false
            end
        else
            if e.head in (:new, :spaltnew, :foreigncall, :cfunction, :new_opaque_closure)
                args = if e.head === :foreigncall
                    fptr = e.args[1]
                    vcat(isatom(fptr) || !istuple_call(fptr) ? compile_args([e.args[1]],        break_labels) : [e.args[1]]
                        list_head(e.args[2:end], 4), 
                        e.args[5:end]
                    )

                end
                if tail
                    emit_return(callex)
                elseif value
                    callex
                else
                    emit(callex)
                end
            elseif e.head === :(=)

            elseif e.head === :block

            elseif e.head === :return

            elseif e.head === :unnecessary

            elseif e.head === :if || e.head === :elseif

            elseif e.head === :_while

            elseif e.head === :_do_while

            elseif e.head === :var"break-block"

            elseif e.head === :break

            elseif e.head === :label || e.head === :symboliclabel
            
            elseif e.head === :symbolicgoto

            elseif e.head === :trycatch || e.head === :tryfinally

            elseif e.head === :newvar

            elseif e.head === :global

            elseif e.head === :var"local-def"
            
            elseif e.head === :local

            elseif e.head === :var"moved-local"

            elseif e.head === :const

            elseif e.head === :isdefined

            elseif e.head === :boundscheck

            elseif e.head === :method

            elseif e.head === :lambda

            elseif e.head === :thunk || e.head === :module

            elseif e.head === :var"toplevel-only"

            elseif e.head === :toplevel

            elseif e.head === :import || e.head === :using || e.head === :export

            elseif e.head === :gc_preserve_begin
                
            elseif e.head in (:line, :meta, :inbounds, :loopinfo, :gc_preserve_end, :aliasscope, :popaliasscope)

            elseif e.head in (:(≔) :(⩴) :(≕) :(:=))
                error("unsupported assignment operator \"$(deparse(e.head))\"")
            elseif e.head === :error
                error(e.args[1])
            else
                error("invalid syntax $(deparse(e))")
            end
        end
    end

end
