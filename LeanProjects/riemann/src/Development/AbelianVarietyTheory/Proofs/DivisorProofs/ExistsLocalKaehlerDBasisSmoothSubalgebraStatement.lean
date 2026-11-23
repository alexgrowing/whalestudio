import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebra
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ), Module.finrank K Ω[K⁄k] = d → ∀ (P : Ideal B) [P.IsPrime], ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧ ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  first | (exact @GlobalTheory.PD.exists_local_dbasis) | (exact GlobalTheory.PD.exists_local_dbasis) | (intros; apply GlobalTheory.PD.exists_local_dbasis  <;> assumption)
