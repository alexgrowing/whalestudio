import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitFiniteSubextensionRingCocone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isColimit_finiteSubextensionRingCocone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω], Nonempty (CategoryTheory.Limits.IsColimit (GlobalTheory.SepCech.ringCocone K Ω)) := by
  first | (exact @GlobalTheory.SepCech.ringCocone_isColimit) | (exact GlobalTheory.SepCech.ringCocone_isColimit) | (intros; apply GlobalTheory.SepCech.ringCocone_isColimit  <;> assumption)
