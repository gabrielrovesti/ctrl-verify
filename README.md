# formal-reactive-systems

> Symbolic formal methods for reactive systems — two self-contained projects
> that share a common theoretical foundation: **BDD-based symbolic reasoning**
> over the state space of concurrent, reactive models.

| Project | Technique | Toolchain | Language |
|---------|-----------|-----------|----------|
| [Supervisory Control Synthesis](#part-1--supervisory-control-synthesis) | Supremal controllable sublanguage (Ramadge–Wonham) | ESCET / CIF 3 | CIF · ToolDef · SVG |
| [Symbolic Model Checking](#part-2--symbolic-model-checking) | Forward/backward BDD fixed-points | PyNuSMV / NuSMV | Python · SMV |

Both projects avoid explicit state enumeration. Instead they represent and
manipulate sets of states as **Binary Decision Diagrams (BDDs)**, making the
algorithms scale to models whose state space would be intractable to enumerate.

---

## Repository Structure

```
formal-reactive-systems/
│
├── supervisory-control/          # Part 1 — CIF/ESCET supervisor synthesis
│   ├── escet/
│   │   ├── factory.cif           # Plant modules + requirements + SVG coupling
│   │   ├── factory.svg           # Graphical interface (live-coupled to CIF)
│   │   └── synthesize.tooldef    # ToolDef script — runs cifdatasynth
│   ├── report.pdf                # Design report (A4, 10 pages)
│   └── README.md                 # Part 1 documentation
│
├── model-checking/               # Part 2 — PyNuSMV model checkers
│   ├── inv_mc.py                 # Invariant (safety) model checker
│   ├── response_mc.py            # Response property (liveness) model checker
│   └── README.md                 # Part 2 documentation
│
└── README.md                     # This file
```

---

## Part 1 — Supervisory Control Synthesis

**Assignment:** SC2542 · 2024-SCQ0089514  
**Toolset:** [ESCET](https://www.eclipse.org/escet/) (Eclipse Supervisory Control Engineering Toolset), CIF 3

### Problem

A two-rover factory automation cell operates on a 6 × 4 grid. A **blue rover**
transports workpieces through a three-stage machining pipeline (M1 → M2 → M3);
an **orange rover** repairs broken machines. Both carry batteries with a capacity
of 8 units, depleted by each move.

Six control requirements must be enforced simultaneously:

| ID | Requirement |
|----|-------------|
| R1 | No rover runs out of battery on a non-charging tile |
| R2 | The sum of both battery levels is always ≥ 1 |
| R3 | The blue rover carries at most 4 workpieces in total |
| R4 | Each rover may only charge when its battery is not full |
| R5 | The two rovers never occupy the same cell simultaneously |
| R6 | If Depot 3 is full, Depot 1 holds at most 1 workpiece |

### Approach

The plant is decomposed into **8 CIF automata** (2 rovers, 3 machines, 3 depots).
R1, R2, R3, R5, R6 are formalised as `requirement inv` invariants; R4 is
enforced at plant level via event guards. The ESCET `cifdatasynth` tool
computes the **supremal controllable and non-blocking sublanguage** via a
BDD-based backward fixed-point, producing a maximally permissive supervisor.

### Quick Start

```bash
# From the supervisory-control/escet/ directory, inside ESCET:
escet synthesize.tooldef          # produces supervisor.cif

# Simulate closed-loop (requires ESCET CLI):
cifsim factory.cif supervisor.cif --svg factory.svg
```

See [`supervisory-control/README.md`](supervisory-control/README.md) for the
full layout, tile positions, SVG coupling table, and design notes.

---

## Part 2 — Symbolic Model Checking

**Assignment:** SC2542 · 2024-SCQ0089514  
**Library:** [PyNuSMV](https://github.com/davidebreso/pynusmv) (Python bindings for NuSMV)

### Problem

Two symbolic model checkers are implemented from scratch using BDDs, without
delegating to NuSMV's built-in engines and without calling `reachable_states`.

#### `inv_mc.py` — Safety / Invariant Verification

Checks `INVARSPEC` properties: whether every reachable state satisfies a
propositional formula `P`.

**Algorithm — BDD forward BFS:**

```
frontiers[0] = init
frontiers[i] = post(frontiers[i-1]) \ (frontiers[0] ∪ … ∪ frontiers[i-1])
```

At each layer, test `frontiers[i] ∩ ¬P ≠ ∅`. On violation, the shortest
counterexample is reconstructed by backward predecessor-chasing through the
stored frontier layers. The trace is a tuple `(s₀, i₀, s₁, i₁, …, sₖ)` of
alternating state-dicts and input-dicts.

#### `response_mc.py` — Liveness / Response Property Verification

Checks `LTLSPEC` properties of the form **G(f → F g)**, where `f` and `g` are
propositional. Non-matching formulas are skipped.

**Algorithm:**

1. **Compute EG(¬g)** — the set of states with *some* infinite ¬g-avoiding
   continuation — as a greatest fixed-point:
   ```
   Z = gfp X . ¬g ∧ pre(X)     (starting from Z = ¬g)
   ```

2. **Violation seeds** = `f ∧ Z`: states where `f` holds and a ¬g-forever path exists.

3. **Forward BFS** from `init` (unrestricted — prefix may cross g-states) to
   detect reachability of any seed.

4. **Lasso counterexample**: prefix (init → seed, same backward reconstruction
   as Part 1) concatenated with a loop (greedily follow successors within Z
   until a state repeats — guaranteed by pigeonhole over the finite set Z).

### Quick Start

```bash
pip install pynusmv          # or install the wheel from the releases page

# Check invariants:
python inv_mc.py path/to/model.smv

# Check response properties:
python response_mc.py path/to/model.smv
```

**Example output — invariant violated:**
```
Property <spec> is an INVARSPEC.
  Invariant is NOT respected
  Counterexample:
    State: {'x': '0', 'mode': 'idle'}
    Input: {'req': '1'}
    State: {'x': '1', 'mode': 'busy'}
```

**Example output — response property violated:**
```
Property G(f -> F g) is an LTLSPEC.
  Formula is NOT respected.
  Counterexample (lasso):
    State: { … }   <- prefix start
    Input: { … }
    State: { … }   <- loop entry (seed)
    Input: { … }
    State: { … }   <- repeated state (loop closes here)
```

See [`model-checking/README.md`](model-checking/README.md) for algorithm
correctness arguments and implementation details.

---

## Shared Theoretical Background

Both projects are grounded in the same symbolic framework:

| Concept | Part 1 (Supervisory Control) | Part 2 (Model Checking) |
|---------|------------------------------|-------------------------|
| State representation | BDD over CIF discrete vars | BDD over SMV state vars |
| Fixed-point direction | Backward (LFP, `pre`) | Forward BFS (safety); Backward GFP (liveness) |
| Correctness guarantee | Maximal permissiveness + non-blocking | Completeness + shortest/minimal counterexample |
| Uncontrollable events | Machine succeed / break | N/A (all transitions symmetric) |
| Counterexample type | Finite path to bad state | Finite path (safety) · Lasso (liveness) |

The connection is deep: supervisor synthesis is itself a fixed-point
computation in the same BDD algebra that the model checkers use to compute
`EG(¬g)` and forward reachability. In both cases correctness is not
verified by inspection — it is *guaranteed structurally* by the fixed-point
theory and the monotonicity of the operators involved.

---

## Requirements

| Tool / Library | Version | Used in |
|----------------|---------|---------|
| [ESCET](https://www.eclipse.org/escet/) | >= 0.9 | Part 1 |
| [PyNuSMV](https://github.com/davidebreso/pynusmv/releases/latest) | latest wheel | Part 2 |
| Python | >= 3.9 | Part 2 |
| NuSMV | bundled with PyNuSMV | Part 2 |

---

## License

Academic coursework. Not licensed for redistribution.
