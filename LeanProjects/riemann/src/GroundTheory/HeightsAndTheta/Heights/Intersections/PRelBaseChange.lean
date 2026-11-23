import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.RelBaseChangeSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial TensorProduct

theorem RelBaseChange.aeval_map {F F' : Type} [Field F] [Field F'] [Algebra F F'] {σ τ : Type}
    (g : σ → MvPolynomial τ F) (p : MvPolynomial σ F) :
    aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (MvPolynomial.map (algebraMap F F') p) =
      MvPolynomial.map (algebraMap F F') (aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, map_X, aeval_X]

theorem RelBaseChange.proof : RelBaseChange.Statement := by
  intro F F' _ _ _ σ τ g
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    erw [RelBaseChange.aeval_map g p, hp, map_zero]
  · intro x hx
    rw [RingHom.mem_ker] at hx
    let Φ : MvPolynomial σ F →ₗ[F] MvPolynomial τ F := (aeval g).toLinearMap
    let eσ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F F'
    let eτ := MvPolynomial.algebraTensorAlgEquiv (σ := τ) F F'
    have key : ∀ y : F' ⊗[F] MvPolynomial σ F,
        eτ (AlgebraTensorModule.lTensor F' F' Φ y) =
          aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (eσ y) := by
      intro y
      induction y with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a p =>
        simp only [AlgebraTensorModule.lTensor_tmul, eσ, eτ, algebraTensorAlgEquiv_tmul, map_smul,
          RelBaseChange.aeval_map, Φ, AlgHom.toLinearMap_apply]
    have hy : eσ.symm x ∈ LinearMap.ker (AlgebraTensorModule.lTensor F' F' Φ) := by
      rw [LinearMap.mem_ker]
      apply eτ.injective
      rw [key, AlgEquiv.apply_symm_apply, hx, map_zero]
    rw [Module.Flat.ker_lTensor_eq] at hy
    obtain ⟨z, hz⟩ := hy
    have hx' : x = eσ (AlgebraTensorModule.lTensor F' F' (LinearMap.ker Φ).subtype z) := by
      rw [hz, AlgEquiv.apply_symm_apply]
    rw [hx']
    clear hz hx'
    induction z with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add]; exact Ideal.add_mem _ hy hz
    | tmul a k =>
      simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype, eσ,
        algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      exact k.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
