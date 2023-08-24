# Observability Tools for Julia

The act of composing packages together is a cornerstone of the Julia ecosystem,
and is further empowered by Julia's excellent multitasking and distributed
computing support. However, this composabilitiy makes it difficult to
understand what all of this code is doing, especially when something goes wrong
deep within the package dependency tree, or when performance as good as desired.

While Debugger.jl and the venerable `println` debugging can help debug issues,
using these tools requires an intimate understanding of package internals and
interactions with other packages, and only gives a local view of package
behavior. Additionally, tools like gdb/rr don't have very convenient Julia
support, and pure-Julia tooling is often package-specific or requires modifying
packages, with often high performance overhead. Pure-Julia tooling also often
only supports a limited number of visualization and analysis backends, causing
users to need to switch between multiple UI tools just to gain a full
understanding of package behavior.

Thankfully, with ProbeBase.jl, we now have powerful pure-Julia tools for
introspecting package behavior and performance, without harming the performance
of carefully-tuned package code, and with flexible support for many kinds of
external pure-Julia and non-Julia backends. ProbeBase currently provides a
single powerful tool, the "tracepoint" (sometimes known as a "probe point"),
which allows packages to expose interesting points of execution within their
codebase to whatever observability tool the user prefers to use.

## Tracepoints Usage

Tracepoints are, at a basic level, just a function call to some user-defined
function, called a "probe". When called, a probe accepts some information about
the tracepoint (a category, whether it's a start or stop event, and some
user-provided arguments), and can do whatever is necessary to log the
tracepoint event for later visualization and analysis.

Let's see a simple example of defining a tracepoint. We have a function
`do_work` which does two pieces of interesting work, and we want to know when
`do_work` is running, and also when each piece of interesting work is running.
We can use the `@region` macro, exported by ProbeBase, to expose this
information:

```julia
module MyMod
    import ProbeBase: @region
    function do_work(x::String, y::Int)
        @region :do_work begin
            @region :do_first_piece x::String begin
                x = do_first_piece(x)
            end
            @region :do_second_piece y::Int begin
                y = do_second_piece(y)
            end
            return (x, y)
        end
    end
    do_first_piece(x) = x * 'd'
    do_second_piece(y) = y+42
end
```

We can now say that `do_work` has been "instrumented" with tracepoints. Note
that we wrap `do_work` in a module - tracepoints are registered at the module
level, and most functions in ProbeBase expect a module to be provided. We also
pass some arguments to our `@region` macros so that we can expose these values
to our probe (which might be interested in their values).

By default, tracepoints are disabled and no probe is loaded. Let's fix this by
defining a probe function that will just print out the category, kind (start or
stop), and arguments for these tracepoints the moment it's called. We'll also
program our tracepoints with this probe using `set_probe_payload`:

```julia
import ProbeBase

function simple_probe(category, kind, _, args...)
    println("Probe triggered: category: $category, kind: $kind, arguments: $args")
    return 0
end

ProbeBase.set_probe_payload(simple_probe, MyMod)
```

Our `simple_probe` is now attached to all of the tracepoints within `MyMod`,
although it's not yet enabled - let's do that now, and see what happens when we
call `do_work`:

```julia
ProbeBase.enable_probes(MyMod)

MyMod.do_work("abc", 123)

# Output:
Probe triggered: category: do_work, kind: start, arguments: ()
Probe triggered: category: do_first_piece, kind: start, arguments: ("abc",)
Probe triggered: category: do_first_piece, kind: finish, arguments: ("abcd",)
Probe triggered: category: do_second_piece, kind: start, arguments: (123,)
Probe triggered: category: do_second_piece, kind: finish, arguments: (165,)
Probe triggered: category: do_work, kind: finish, arguments: ()
```

We can see that the `@region` macro creates two tracepoints: a start tracepoint
at the start of the macro region, and a finish tracepoint at the end of the
region. We can see how the categories line up as expected, and that `@region`
calls can be safely nested. Also, we see that the arguments are evaluated at
each tracepoint site, so we get to see the results of calling `do_first_piece`
and `do_second_piece`.
