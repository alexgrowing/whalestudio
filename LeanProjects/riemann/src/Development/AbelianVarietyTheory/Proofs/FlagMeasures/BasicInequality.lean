import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BasicIneq

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) :
    ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P := by
  rw [ofReal_norm_eq_enorm]
  unfold Frames.amp Frames.mass
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun o => ?_)
  split_ifs with h
  · obtain ⟨p, hp⟩ := h.1
    have h1 : ‖S.om d o.out‖ = 1 := (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have h2 : 0 ≤ S.mu o.out := by
      unfold Frames.mu invVol
      positivity
    rw [← ofReal_norm_eq_enorm, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_of_nonneg h2]
  · simp

theorem basic_inequality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → (∀ d P, ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P) ∧ ∀ (P : S.Datum → Submodule L.O S.V → Prop) (B ε : ℝ), 0 ≤ ε → (∀ d, S.mass d (P d) ≤ ENNReal.ofReal (B)) → (∀ d, ENNReal.ofReal (‖S.amp d (P d)‖) ≤ ENNReal.ofReal (ε) * S.mass d (P d)) → S.ampSq P ≤ ENNReal.ofReal (ε ^ 2 * B) * S.sumData fun d => S.mass d (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _
  refine ⟨amp_le_mass L r k S, fun P B ε hε hB hA => ?_⟩
  unfold Frames.ampSq Frames.sumData
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  beta_reduce
  rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul (sq_nonneg ε), ENNReal.ofReal_pow hε]
  calc ENNReal.ofReal ‖S.amp o.out (P o.out)‖ ^ 2
      ≤ (ENNReal.ofReal ε * S.mass o.out (P o.out)) ^ 2 := by
        gcongr
        exact hA _
    _ = ENNReal.ofReal ε ^ 2 * S.mass o.out (P o.out) * S.mass o.out (P o.out) := by ring
    _ ≤ ENNReal.ofReal ε ^ 2 * ENNReal.ofReal B * S.mass o.out (P o.out) := by
        gcongr
        exact hB _

end GlobalTheory.HL.BasicIneq
