import ProbeBase
using Test

function eval_new_mod(ex)
    eval(
        :(module ProbedModule
            using ProbeBase

            # Our instrumented function
            function myfunc(x::String, y::Int)
                $ex
            end
        end)
    )
end

const vec = []
function probe(category::Symbol, kind::Symbol, lib_id::Int, args::NamedTuple)
    push!(vec, (category, kind, lib_id, args))
    return lib_id + 1
end

@testset "@region" begin
    function test_region(ex;
                         x_pre="test", y_pre=42,
                         x_all=nothing, y_all=nothing,
                         with_x=true, with_y=true,
                         flip=false,
                         valid=true)
        mod = eval_new_mod(ex)
        valid && @test @invokelatest(mod.myfunc("test", 42)) == "testn43"
        @test length(vec) == 0

        ProbeBase.set!(probe, mod)
        valid && @test @invokelatest(mod.myfunc("test", 42)) == "testn43"
        @test length(vec) == 0

        ProbeBase.enable!(mod)
        if valid
            @test @invokelatest(mod.myfunc("test", 42)) == "testn43"
        else
            @invokelatest(mod.myfunc("test", 42))
            error("unreachable") # This should never be hit anyway
        end
        @test length(vec) == 2

        region_start = popfirst!(vec)
        region_finish = popfirst!(vec)

        ProbeBase.disable!(mod)
        valid && @test @invokelatest(mod.myfunc("test", 42)) == "testn43"
        @test length(vec) == 0

        cat, kind, lib_id, args = region_start
        @test cat == :test
        @test kind == :start
        @test lib_id == 0
        function test_args_fields(args, flip, with_x, with_y, x_exp, y_exp)
            exp = []
            if with_x
                push!(exp, :x)
            end
            if with_y
                push!(exp, :y)
            end
            if flip
                exp = reverse(exp)
            end
            args_fs = fieldnames(typeof(args))
            @test length(exp) == length(args_fs)
            if length(exp) == length(args_fs)
                @test all(exp .== args_fs)
                if with_x
                    @test args.x == x_exp
                end
                if with_y
                    @test args.y == y_exp
                end
            end
        end
        test_args_fields(args, flip, with_x, with_y,
                         something(x_all, x_pre),
                         something(y_all, y_pre))

        cat, kind, lib_id, args = region_finish
        @test cat == :test
        @test kind == :finish
        @test lib_id == 1
        test_args_fields(args, flip, with_x, with_y,
                         something(x_all, x_pre * 'n'),
                         something(y_all, y_pre + 1))
    end

    # As-is
    test_region(:(@region :test x::String y::Int begin
        x *= 'n'
        y += 1
        x * repr(y)
    end))

    # Less args
    test_region(:(@region :test begin
        x *= 'n'
        y += 1
        x * repr(y)
    end); with_x=false, with_y=false)
    test_region(:(@region :test x::String begin
        x *= 'n'
        y += 1
        x * repr(y)
    end); with_y=false)

    # Any order
    test_region(:(@region :test y::Int x::String begin
        x *= 'n'
        y += 1
        x * repr(y)
    end); flip=true)

    # Identical start+finish override
    test_region(:(@region :test x::String="abc" y::Int begin
        x *= 'n'
        y += 1
        x * repr(y)
    end); x_all="abc")
    test_region(:(@region :test x::String y::Int=99 begin
        x *= 'n'
        y += 1
        x * repr(y)
    end); y_all=99)
    test_region(:(@region :test x::String="abc" y::Int=99 begin
        x *= 'n'
        y += 1
        x * repr(y)
    end); x_all="abc", y_all=99)

    # TODO: Different start+finish override

    # Undefined variable
    @test_throws UndefVarError test_region(:(@region :test z::Int nothing); valid=false)

    # Missing type
    @test_throws ArgumentError test_region(:(@region :test x nothing); valid=false)

    # Bad category
    @test_throws ArgumentError test_region(:(@region "test" x::String nothing); valid=false)
    @test_throws ArgumentError test_region(:(begin
        cat = :test
        @region cat x::String nothing
    end); valid=false)
end
