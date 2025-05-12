# Proof of strong normalisation for the AEff language

- The formalisation has been tested with Agda version 2.7.0 and standard library version 2.1.

- The unicode symbols used in the source code have tested to display correctly with the DejaVu Sans Mono font.

#### Definition of the AEff language

- `EffectAnnotations.agda` - effect annotations for signals and interrupt handlers

- `Types.agda` - value, computation, and process types

- `AEff.agda` - well-typed values, computations, and processes (we do not consider untyped terms)

- `Renamings.agda` - renamings for values, computations, and processes

- `Substitutions.agda` - substitutions for values, computations, and processes

- `Preservation.agda` - small-step operational semantics for computations (also serves as a preservation proof)

- `AwaitingComputations.agda` - characterisation of computations that are temporarily blocked awaiting a promise

- `Progress.agda` - proof of progress for the small-step operational semantics of computations

- `ProcessPreservation.agda` - small-step operational semantics for processes (also serves as a preservation proof)

- `ProcessProgress.agda` - proof of progress for the small-step operational semantics of processes

- `Finality.agda` - proof that the result forms of computations are final, i.e., they do not reduce further

- `ProcessFinality.agda` - proof that the result forms of processes are final, i.e., they do not reduce further

#### Proof of strong normalisation for the AEff language

- `AEffStar/` - definition of the simplified language without effect annotations and with the promise-typed constant ★ and proof of strong normalisation for it

    - `AEffStar/AEffStar.agda` - definition of AEffStar: types, values, computations, renamings, substitutions and small-step operational semantics
    
    - `AEffStar/SubstitutionProperties.agda` - proof of a number of substitution properties to be used elsewhere in the proof

    - `AEffStar/StrongNormalisation.agda` - definition of strong normalisation with and without the bound on the length of reduction sequences, and proof that both definitions are equivalent

    - `AEffStar/Continuations.agda` - definition of term-abstractions, continuations and their application to computations, and proof about how application interacts with reductions

    - `AEffStar/Reducibility.agda` - definition of reducibility, proof that reducibility implies strong normalisation, proof of the fundamental theorem of logical relations, and the result that the calculus is strongly normalising

- `Simulation.agda` - proof that AEffBsn is a conservative extension of AEff which is then used to prove that AEff is strongly normalising
