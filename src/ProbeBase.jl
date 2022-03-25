module ProbeBase

using Preferences

abstract type AbstractPayload end

function null_payload(x...) end

struct ProbeSpec
    lineno::LineNumberNode
    kind::Symbol
    argtypes::Vector{DataType}
    payload::Base.RefValue{Ptr{Cvoid}}
    semaphore::Threads.Atomic{Int}
end
ProbeSpec(lineno::LineNumberNode, kind::Symbol, argtypes::Vector, payload::Ptr{Cvoid}) =
    ProbeSpec(lineno, kind, argtypes,
              Ref(payload), Threads.Atomic{Int}(PROBES_ENABLED))
ProbeSpec(lineno::LineNumberNode, kind::Symbol, argtypes::Vector) =
    ProbeSpec(lineno, kind, argtypes,
              # null_payload is varargs, and doesn't use arguments anyway
              Ref(@cfunction(null_payload, Cvoid, ())),
              Threads.Atomic{Int}(PROBES_ENABLED))

const PROBES = Dict{Module,Dict{Symbol,ProbeSpec}}()
const PROBES_FUNC = Dict{Module,Dict{Symbol,Any}}()
const PROBES_ENABLED = parse(Bool, @load_preference("default_enabled", "false"))
const PROBES_LOCK = Threads.ReentrantLock()

default_enabled(val::Bool) = @set_preferences!("default_enabled" => repr(val))

function set_probe_payload(mod::Module, category::Symbol, payload::Ptr{Cvoid})
    lock(PROBES_LOCK) do
        PROBES[mod][category].payload[] = payload
    end
end
function set_probe_payload(f, mod::Module, category::Symbol)
    spec = nothing
    lock(PROBES_LOCK) do
        spec = PROBES[mod][category]
        PROBES_FUNC[mod][category] = f
    end
    ptr = eval(:(@cfunction($f, Cvoid, ($(spec.argtypes...),))))
    set_probe_payload(mod, category, ptr)
end
function enable_probe(mod::Module, category::Symbol)
    spec = lock(PROBES_LOCK) do
        PROBES[mod][category]
    end
    Threads.atomic_add!(spec.semaphore, 1)
end
function disable_probe(mod::Module, category::Symbol)
    spec = lock(PROBES_LOCK) do
        PROBES[mod][category]
    end
    Threads.atomic_sub!(spec.semaphore, 1)
end
function enable_probes(mod::Module)
    lock(PROBES_LOCK) do
        for spec in values(PROBES[mod])
            Threads.atomic_add!(spec.semaphore, 1)
        end
    end
end
function disable_probes(mod::Module)
    lock(PROBES_LOCK) do
        for spec in values(PROBES[mod])
            Threads.atomic_sub!(spec.semaphore, 1)
        end
    end
end

probe_enabled(spec::ProbeSpec) = spec.semaphore[] > 0
@generated function probe_trigger(spec::ProbeSpec, args...)
    Targs = Expr(:tuple, map(nameof, args)...)
    ex = Expr(:call, :ccall, :(spec.payload[]), :Cvoid, Targs)
    for (idx, arg) in enumerate(args)
        push!(ex.args, :(args[$idx]))
    end
    ex
end
function probe_maybe_trigger(spec::ProbeSpec, kind::Symbol, args...)
    if probe_enabled(spec)
        probe_trigger(spec, args...)
    end
end

function parse_args(args)
    argnames = Symbol[]
    argtypes = DataType[]
    argvalues = Expr[]
    for arg in args.args
        if Meta.isexpr(arg, :(=))
            push!(argnames, arg.args[1].args[1])
            push!(argtypes, eval(arg.args[1].args[2]))
            push!(argvalues, esc(arg.args[2]))
        elseif Meta.isexpr(arg, :(::))
            push!(argnames, arg.args[1])
            push!(argtypes, eval(arg.args[2]))
            push!(argvalues, esc(arg.args[1]))
        else
            throw(ArgumentError("Cannot handle expr with head: $(arg.head)"))
        end
    end
    (;argnames, argtypes, argvalues)
end
function register_probe(mod::Module, category::Symbol, spec::ProbeSpec; enable=false)
    if enable
        spec.semaphore[] = 1
    end
    lock(PROBES_LOCK) do
        module_specs = get!(PROBES, mod) do
            Dict{Symbol,ProbeSpec}()
        end
        module_specs[category] = spec
        (get!(PROBES_FUNC, mod) do
            Dict{Symbol,Any}()
        end)[category] = nothing
    end
end
macro probe(kind::QuoteNode, category::QuoteNode, args=Expr(:tuple))
    argspec = parse_args(args)
    spec = ProbeSpec(__source__, kind.value, argspec.argtypes)
    register_probe(__module__, category.value, spec)
    :(probe_maybe_trigger($spec, $kind, $(argspec.argvalues...)))
end
#= FIXME
macro probe_start(category::Symbol)
    :(probe($spec, :start))
end
macro probe_stop(category::Symbol)
    :(probe($spec, :stop))
end
macro probe_event(category::Symbol)
    :(probe($spec, :event))
end
=#

end # module
