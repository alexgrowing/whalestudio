import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBund
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  first | (exact @GlobalTheory.EtC.pbf_disc_model) | (exact GlobalTheory.EtC.pbf_disc_model) | (intros; apply GlobalTheory.EtC.pbf_disc_model  <;> assumption)
