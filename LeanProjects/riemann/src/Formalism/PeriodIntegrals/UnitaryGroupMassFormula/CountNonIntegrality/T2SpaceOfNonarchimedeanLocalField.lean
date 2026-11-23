import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DSurjDef

noncomputable section

namespace PI.CntNotIntW

open scoped TensorProduct
open ValuativeRel

theorem t2Space_of_nonarchimedeanLocalField' (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] :
    T2Space Fp := by
  have : T0Space Fp := by
    refine ⟨fun x y hxy => ?_⟩
    by_contra hne
    have hv : valuation Fp (y - x) ≠ 0 :=
      (valuation Fp).ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hs : {z : Fp | z ≠ y} ∈ nhds x := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hv, ?_⟩
      rintro _ ⟨z, hz, rfl⟩ h
      have h' : x + z = y := h
      have hz' : valuation Fp z < valuation Fp (y - x) := hz
      have hzy : z = y - x := by rw [← h']; ring
      rw [hzy] at hz'
      exact lt_irrefl _ hz'
    rw [hxy.nhds_eq] at hs
    exact (mem_of_mem_nhds hs : y ≠ y) rfl
  infer_instance

theorem tensorLiftSurjective : PiSurj := by
  unfold PiSurj
  intro K _ _ ℓ _ Fp _ _ _ _ _ _ hcont hfin ι hdense
  have : T2Space Fp := t2Space_of_nonarchimedeanLocalField' Fp
  have : FiniteDimensional ℚ_[ℓ] Fp := hfin
  have : ContinuousSMul ℚ_[ℓ] Fp := by
    constructor
    have h : (fun p : ℚ_[ℓ] × Fp => p.1 • p.2) = fun p => algebraMap ℚ_[ℓ] Fp p.1 * p.2 := by
      funext p
      exact Algebra.smul_def _ _
    rw [h]
    exact (hcont.comp continuous_fst).mul continuous_snd
  let S : Submodule ℚ_[ℓ] Fp := LinearMap.range (piMap K ℓ Fp ι).toLinearMap
  have hS : IsClosed (S : Set Fp) := S.closed_of_finiteDimensional
  have hsub : Set.range ι ⊆ (S : Set Fp) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨1 ⊗ₜ y, piMap_one_tmul K ℓ Fp ι y⟩
  intro z
  obtain ⟨w, hw⟩ := closure_minimal hsub hS (hdense z)
  exact ⟨w, hw⟩

end PI.CntNotIntW
