# Tendermint Consensus specification in Quint

A Quint specification of Tendermint consensus, based on the
[paper](https://arxiv.org/abs/1807.04938), using the Consensus State Machine
Interface (CSMI) library.

## Model

The model is reactive to messages. Transitions in the state machine are either a message being received or a timeout expiring. In Tendermint, the same message can trigger many "upon" events, and the paper states that it doesn't matter in which order they are processed, so we model an arbitrary order. Also, all reactions to a single message are done in one atomic step.

We don't model multiple consensus instances. Execution finishes after consensus is reached for the first time. It should be straightforward to adapt this to multiple instances.

We also keep track of evidence to check for detecting faulty nodes in fork scenarios. This is kept in a `bookkeeping` field, which is not used by the protocol itself, only to check properties.

## Properties

We define agreement, validity and accountability.

To check that they hold in with a small enough percentage of faulty nodes, run the simulator:

``` sh
$ quint run tendermint_tests.qnt --max-steps=50 --invariant="agreement and validity and accountability"
```

Accountability should also hold with a larger number of faulty nodes.
*FIXME:* why doesn't agreement and validity break on more than 1/3 faulty nodes?

``` sh
$ quint run tendermint_tests.qnt --max-steps=50 --invariant=accountability --main tendermint_faulty
```

### Liveness

We don't define liveness in this spec. The closes thing to liveness we check is that the model can reach decision in some executions by checking that the property `no_decision` is violated. The following command should result in a violation, and present a trace exemplifying how decision can be reached:

``` sh
$ quint run tendermint_tests.qnt --max-steps=50 --invariant=no_decision
```

## Tests

In [`tendermint_tests.qnt`](./tendermint_tests.qnt) we have a test setup and one test case (for now) describing how we can reach specific scenarios. For now, we describe how we can get to a state where the "upon" statement from line 28 of the pseudocode is called, which requires a very specific setting and it is not obvious when it comes into play. The test should help a reader understand how that is possible, and loading that test in the REPL can enable them to explore the state further.

```sh
$ quint -r tendermint_tests.qnt::tendermint_tests
Quint REPL 0.24.0
Type ".exit" to exit, or ".help" for more information
>>> line28Test
true
>>> CSMI::s
```

To simply run the test, you can use:

```sh
$ quint test tendermint_tests.qnt
```

## Using Breakpoints

Quint doesn't support breakpoints natively, but it is easy to improvise one. For this model, we added a `Breakpoint` output that will set the `breakpoint` field in `bookkeeping` to `true`. We then define an invariant stating that `bookkeeping.breakpoint` is never true, and run the Quint simulator with this invariant:

```sh
$ quint run tendermint_tests.qnt --max-steps=50 --invariant="bookkeeping"
```

Which should result in a violation with the trace up to the point where the breakpoint got triggered.

If you want to interact with that trace, you can also call it from the REPL:

``` sh
$ quint -r tendermint_tests.qnt::tendermint_tests
Quint REPL 0.24.0
Type ".exit" to exit, or ".help" for more information
>>> q::test(10000, 50, 1, init, step, breakpoint)
false
>>> q::lastTrace
// shows the entire trace
>>>
```

