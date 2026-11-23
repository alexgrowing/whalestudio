import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLastMeasMeasurePreserving
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BcUnique

theorem headLastMeas_symm_one (p : V 1 × ℂ) :
    (GlobalTheory.LocFub.headLastMeas 1).symm p = appendV 1 1 (p.1, EuclideanSpace.single 0 p.2) := by
  rw [MeasurableEquiv.symm_apply_eq, GlobalTheory.LocFub.headLastMeas_apply]
  refine Prod.ext ?_ ?_
  · ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  · show p.2 = appendV 1 1 (p.1, EuclideanSpace.single 0 p.2) (Fin.last 1)
    rw [appendV_last]
    simp

theorem integral_eq_integral_last_head (f : V (1 + 1) → ℝ) (hf : Integrable f) :
    ∫ x, f x = ∫ w : ℂ, ∫ v : V 1, f (appendV 1 1 (v, EuclideanSpace.single 0 w)) := by
  have hmp := (GlobalTheory.LocFub.headLastMeas_measurePreserving 1).symm (GlobalTheory.LocFub.headLastMeas 1)
  have hI : Integrable (f ∘ (GlobalTheory.LocFub.headLastMeas 1).symm)
      ((volume : Measure (V 1)).prod (volume : Measure ℂ)) :=
    (hmp.integrable_comp_emb (GlobalTheory.LocFub.headLastMeas 1).symm.measurableEmbedding).2 hf
  calc ∫ x, f x = ∫ z, f ((GlobalTheory.LocFub.headLastMeas 1).symm z)
          ∂((volume : Measure (V 1)).prod (volume : Measure ℂ)) := (hmp.integral_comp' f).symm
    _ = ∫ w : ℂ, ∫ v : V 1, f ((GlobalTheory.LocFub.headLastMeas 1).symm (v, w)) := integral_prod_symm _ hI
    _ = _ := by simp only [headLastMeas_symm_one]

end GlobalTheory.BcUnique
