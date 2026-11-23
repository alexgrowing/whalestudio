import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.BoxEqConvexBodyLT

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable (K : Type) [Field K] [NumberField K]

def unitMul (u : (𝓞 K)ˣ) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.mulLeft ℝ (mixedEmbedding K (u : K))

theorem unitMul_apply (u : (𝓞 K)ˣ) (y : mixedSpace K) : unitMul K u y = u • y := rfl

theorem unitMul_comp (u v : (𝓞 K)ˣ) : unitMul K u ∘ₗ unitMul K v = unitMul K (u * v) := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, unitMul_apply, mul_smul]

theorem unitMul_det_ne_zero (u : (𝓞 K)ˣ) : LinearMap.det (unitMul K u) ≠ 0 := by
  intro h
  have h1 : unitMul K u ∘ₗ unitMul K u⁻¹ = LinearMap.id := by
    rw [unitMul_comp, mul_inv_cancel]
    refine LinearMap.ext fun y => ?_
    rw [unitMul_apply, one_smul, LinearMap.id_apply]
  have := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, h, zero_mul, LinearMap.det_id] at this
  exact zero_ne_one this

theorem preimage_box (u : (𝓞 K)ˣ) :
    (unitMul K u) ⁻¹' (box K fun _ => 1) = box K (fun w => (w (u : K))⁻¹) := by
  ext y
  simp only [Set.mem_preimage, box, Set.mem_ofPred_eq, unitMul_apply, unitSMul_smul, map_mul,
    normAtPlace_apply]
  refine forall_congr' fun w => ?_
  have hw : 0 < w (u : K) := by
    refine w.pos_iff.2 ?_
    simp
  rw [← one_div, lt_div_iff₀' hw]

theorem prod_inv_unit (u : (𝓞 K)ˣ) : ∏ w : InfinitePlace K, ((w (u : K))⁻¹) ^ mult w = 1 := by
  simp_rw [inv_pow]
  rw [Finset.prod_inv_distrib, prod_eq_abs_norm, Units.norm, Rat.cast_one, inv_one]

theorem vfac_ne_zero : vfac K ≠ 0 := by
  unfold vfac
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ ?_)
  exact_mod_cast NNReal.pi_ne_zero

theorem vfac_ne_top : vfac K ≠ ⊤ := by
  unfold vfac
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem unitPreserving : UnitPreserving := by
  intro K _ _ u
  have hdet := unitMul_det_ne_zero K u
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (mixedSpace K)) hdet
  have hpre := Measure.addHaar_preimage_linearMap
    (volume : Measure (mixedSpace K)) hdet (box K fun _ => 1)
  have hw : ∀ w : InfinitePlace K, 0 < (w (u : K))⁻¹ := fun w =>
    inv_pos.2 (w.pos_iff.2 (by simp))
  rw [preimage_box, boxVolume K _ hw, boxVolume K _ (fun _ => one_pos), prod_inv_unit] at hpre
  simp only [one_pow, Finset.prod_const_one, ENNReal.ofReal_one, mul_one] at hpre
  have hc : ENNReal.ofReal |(LinearMap.det (unitMul K u))⁻¹| = 1 :=
    (ENNReal.mul_left_inj (vfac_ne_zero K) (vfac_ne_top K)).1 (by rw [one_mul]; exact hpre.symm)
  rw [hc, one_smul] at hmap
  exact ⟨(unitMul K u).continuous_of_finiteDimensional.measurable, hmap⟩

end PI.Residue
