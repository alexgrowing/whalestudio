import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace PI.Residue

theorem box_eq_convexBodyLT (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ)
    (hr : ∀ w, 0 < r w) : box K r = convexBodyLT K (fun w => (r w).toNNReal) := by
  ext y
  simp only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall, Real.coe_toNNReal _ (hr _).le]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · simpa [normAtPlace_apply_of_isReal hw] using h w
    · simpa [normAtPlace_apply_of_isComplex hw] using h w
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw

theorem boxVolume : BoxVolume := by
  intro K _ _ r hr
  rw [box_eq_convexBodyLT K r hr, convexBodyLT_volume, vfac]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => (pow_pos (hr w) _).le)]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_pow (hr w).le]
  rfl

end PI.Residue
