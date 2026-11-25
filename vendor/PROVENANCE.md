# Logarithmic separation for powers of two and three

Eric Merle wrote the Lean proofs in this directory. They are adapted from the `logs23/Logs23` directory of [One Obstruction, Three Faces, commit cd92689](https://github.com/ericmerle3789/one-obstruction-three-faces-lean/tree/cd92689908fabd161d06ffdb04b43bb83a5894e0/logs23). The original work and these adaptations are distributed under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/). The license text is in `LICENSE`.

The selection retains the proof of `Logs23.lam_lower_thm`. The definition `Steiner.Lam` comes from `steiner1978/Steiner/Steiner_Enonces.lean` in the same commit and is extracted in `Logs23/Lam.lean`. The source files `Logs23_Enonces.lean`, `TwoLog_Enonces.lean`, `Pont.lean` and `TwoLog.lean` use the extracted definition. Statements, imports and conclusions about Collatz cycles that lie outside the dependency chain of the logarithmic bound were removed.
