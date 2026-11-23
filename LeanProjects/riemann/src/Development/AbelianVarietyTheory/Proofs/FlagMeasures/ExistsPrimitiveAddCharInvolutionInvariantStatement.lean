import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_addChar_involution_invariant : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  first | exact @GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | exact GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | (intros; apply GlobalTheory.GramCount.exists_isPrimitive_invol_invariant <;> assumption)
