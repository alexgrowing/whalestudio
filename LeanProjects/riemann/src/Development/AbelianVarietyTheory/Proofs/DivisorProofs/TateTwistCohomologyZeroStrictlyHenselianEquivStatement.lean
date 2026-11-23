import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (exact GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (intros; apply GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv  <;> assumption)
