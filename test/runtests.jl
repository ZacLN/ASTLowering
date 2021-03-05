using Test, Lowering, SExpressions, CSTParser

function stoExpr(s)
    if s isa List
        if isnil(s)
            ()
        elseif isnil(cdr(s))
            car(s)
        else
            @assert car(s) isa Symbol
            Expr(car(s), [stoExpr(a) for a in cdr(s)]...)
        end
    else
        s
    end
end


function replace_reps(s)
    m = match(r"#(\d+)=", s)
    while m !== nothing
        io = IOBuffer(s)
        seek(io, m.offset + sizeof(m.match)-1)
        obj = SExpressions.Parser.nextobject(io)
        val = sprint(show, obj.value)
        s = replace(s, m.match => "", count = 1)
        s = replace(s, "#$(m.captures[1])#" => val)
        m = match(r"#(\d+)=", s)
    end
    s
end


function scm_lower(e)
    # requires build of julia w/ C interface to jl_expand0 that returns a string of the lowered code
    s = ccall(:jl_expand0, Any, (Any, Any), e, Main)
    if s isa Expr  && s.head == :error
        s = "(error \"$(s.args[1])\")"
    end
    
    # strip 
    # m = match(r"#(\d+)=\(ssavalue (\d+)\)", s)
    # while m !== nothing
    #     s = replace(s, r"#(\d+)=\(ssavalue (\d+)\)" => "(ssavalue $(m.captures[1]))")
    #     m = match(r"#(\d+)=\(ssavalue (\d+)\)", s)
    # end
    s = replace_reps(s)

    m = match(r"#(\d+)#", s)
    while m !== nothing
        s = replace(s, r"#(\d+)#" => "(ssavalue $(m.captures[1]))")
        m = match(r"(#(\d+)#)", s)
    end

    m = match(r"#\d+=", s)
    while m !== nothing
        s = replace(s, r"#\d+=" => "")
        m = match(r"#\d+=", s)
    end

    l = SExpressions.Parser.parse(s)
    stoExpr(l)
end


function compare_lowered(a, b)
    r = if a isa Expr && b isa Expr
        if a.head === b.head === :ssavalue
            true
        else
            compare_lowered(a.head, b.head) && all(x -> compare_lowered(x[1], x[2]), zip(a.args, b.args))
        end
    elseif a isa LineNumberNode && b isa LineNumberNode || (a isa LineNumberNode && b isa Expr && b.head == :line) || (b isa LineNumberNode && a isa Expr && a.head == :line)
        true
    elseif a isa Symbol && b isa Symbol
        a == b || 
        ((string(a) == "#self#" && string(b) == "_self_") || (string(b) == "#self#" && string(a) == "_self_")) || 
        (occursin(r"^#s\d+$", String(a)) && occursin(r"^#s\d+$", String(b))) ||
        equiv_namedsym(String(a), String(b))
        
    else
        a == b
    end
    !r && @info a,b
    r
end

function equiv_namedsym(a, b)
    ma = match(r"#(\S*)#\d+", a)
    ma === nothing && return false
    mb = match(r"#(\S*)#\d+", b)
    mb === nothing && return false
    ma.captures[1] == mb.captures[1]
end

using SExpressions.Parser: Dot, SExpression, skipws, skipcomment, nextobject, readobjectsuntil, listify, _READER_MACROS, parsestring, readsymbol, tryparse, closer
function SExpressions.Parser.nextobject(io::IO) :: Union{Some{<:Union{Dot, SExpression}}, Nothing}
    skipws(io)
    if eof(io)
        return nothing
    end

    c = peek(io, Char)
    if c == ';'
        skipcomment(io)
        nextobject(io)
    elseif c in "([{"
        read(io, Char)
        cl = closer(c)
        objects = readobjectsuntil(io, cl)
        Some(listify(objects))
    elseif c in ")]}"
        error("mismatched superfluous $c")
    elseif c in keys(_READER_MACROS)
        read(io, Char)
        nextobj = nextobject(io)
        if nextobj === nothing
            error("lonely reader macro $c")
        else
            Some(List(_READER_MACROS[c], something(nextobj)))
        end
    elseif c == '"'
        read(io, Char)
        Some(parsestring(io))
    # elseif c == '#'
    #     read(io, Char)
    #     Some(readhash(io))
    else
        str = readsymbol(io)
        if str == "."
            Some(Dot())
        else
            asnumber = tryparse(Number, str)
            Some(something(asnumber, Symbol(str)))
        end
    end
end

macro test_lowering(e0)
    quote
        let e = CSTParser.remlineinfo!($(Expr(:quote,e0)))
            l1 = Lowering.expand_forms(e)
            l2 = scm_lower(e)
            @test compare_lowered(l1, l2)
        end
    end
end





e = CSTParser.remlineinfo!(:(function f(a = 1, b = a) end))
e1 = Lowering.expand_forms(e)
e2 = scm_lower(e)
compare_lowered(e1, e2)

io = IOBuffer("(a)")
SExpressions.Parser.nextobject(io)



@testset "pass 1" begin
@testset ":let" begin
    @test_lowering let; end
    @test_lowering let x ; end
    @test_lowering let x = 1; end
    @test_lowering let x::T = 1; end
    @test_lowering let (x,y) = 1 ; end
    @test_lowering let x = 1, y = 1; end
end

@testset ":let" begin
    @test_lowering begin end
    @test_lowering begin x end
    @test_lowering begin begin x end end
end

@testset ":for" begin
    @test_lowering for i = I end
    @test_lowering for i = I body end
    @test_lowering for i = I, j = J end
    @test_lowering for outer i = I, j = J end
end

@testset ":vect" begin
    @test_lowering [a, b]
    @test_lowering [a, b; c]
    @test_lowering [a = b]
end

@testset ":hcat" begin
    @test_lowering [a b]
    @test_lowering [a b = 1]
end

@testset ":vcat" begin
    @test_lowering [a;b]
    @test_lowering [a;b = 1]
end

@testset ":typed_hcat" begin
    @test_lowering T[a b]
    @test_lowering T[a b = 1]
end

@testset ":typed_vcat" begin
    @test_lowering T[a; b]
    @test_lowering T[a; b = 1]
end

@testset ":function " begin
    @test_lowering function f end
    @test_lowering function f() end
    @test_lowering function f(a) end
    @test_lowering function f(a, b) end
    
    @test_lowering function f(a = 1) end
    @test_lowering function f(a, b = 2) end
    @test_lowering function f(a = 1, b = 2) end
    @test_lowering function f(a = 1, b = a) end
    @test_lowering function f(a = 1, b = a, c = b) end
    @test_lowering function f(a = 1, b = a, c = b) end

    @test_lowering function f(;p = 1) end
    @test_lowering function f(a, b = 1;p = 1) end
end


@testset ":->" begin
    @test_lowering a -> a
end
@testset ":try" begin
Lowering.expand_forms(:(try blk catch end))
Lowering.expand_forms(:(try blk catch e end))
Lowering.expand_forms(:(try blk catch e eblk end))
Lowering.expand_forms(:(try blk catch e eblk finally fblk end))
end
@testset ":lambda" begin

end
@testset ":block" begin
Lowering.expand_forms(:(begin x = 1; y = 2 end))
end
# @testset ":unionall" begin
# end
@testset ":for" begin
Lowering.expand_forms(:(for i = 1:10 end))
end
end