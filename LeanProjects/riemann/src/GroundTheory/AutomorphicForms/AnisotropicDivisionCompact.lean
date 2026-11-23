import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicDivision
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable (K : Type*) [Field K] [NumberField K] (D : Type*) [DivisionRing D] [Algebra K D]

abbrev adeleTensorTopology : TopologicalSpace (𝔸[K] ⊗[K] D) :=
  moduleTopology 𝔸[K] (𝔸[K] ⊗[K] D)

attribute [local instance] adeleTensorTopology

theorem isModuleTopology_adeleTensor : IsModuleTopology 𝔸[K] (𝔸[K] ⊗[K] D) := ⟨rfl⟩

attribute [local instance] isModuleTopology_adeleTensor

theorem isTopologicalRing_adeleTensor [FiniteDimensional K D] :
    IsTopologicalRing (𝔸[K] ⊗[K] D) :=
  IsModuleTopology.isTopologicalRing 𝔸[K] _

attribute [local instance] isTopologicalRing_adeleTensor

def rationalUnits : Dˣ →* (𝔸[K] ⊗[K] D)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : D →ₐ[K] 𝔸[K] ⊗[K] D).toRingHom.toMonoidHom

def scalarUnits : (𝔸[K])ˣ →* (𝔸[K] ⊗[K] D)ˣ :=
  Units.map (algebraMap 𝔸[K] (𝔸[K] ⊗[K] D)).toMonoidHom

variable {K D}

theorem baseMap_ofId_eq_includeRight (ξ : K ⊗[K] D) :
    baseMap (Algebra.ofId K 𝔸[K]) ξ =
      Algebra.TensorProduct.includeRight (Algebra.TensorProduct.lid K D ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    rw [baseMap, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
      Algebra.TensorProduct.includeRight_apply, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem rationalUnits'_eq (ξ : (K ⊗[K] D)ˣ) :
    rationalUnits' ξ = rationalUnits K D
      (Units.map (Algebra.TensorProduct.lid K D : K ⊗[K] D →ₐ[K] D).toRingHom.toMonoidHom ξ) :=
  Units.ext (baseMap_ofId_eq_includeRight (ξ : K ⊗[K] D))

variable [FiniteDimensional K D] {d : ℕ} (b : Basis (Fin d) K D)

theorem continuous_coords_adele : Continuous (coords b 𝔸[K]) :=
  IsModuleTopology.continuous_of_linearMap (coords b 𝔸[K]).toLinearMap

theorem continuous_coords_adele_symm : Continuous (coords b 𝔸[K]).symm := by
  have h : ⇑(coords b 𝔸[K]).symm = fun y => ∑ k, y k • baseBasis b 𝔸[K] k := by
    funext y
    exact Module.Basis.equivFun_symm_apply _ y
  rw [h]
  exact continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const

def coordsHomeomorph : 𝔸[K] ⊗[K] D ≃ₜ (Fin d → 𝔸[K]) where
  toEquiv := (coords b 𝔸[K]).toEquiv
  continuous_toFun := continuous_coords_adele b
  continuous_invFun := continuous_coords_adele_symm b

variable (K D) in
theorem t2Space_adeleTensor : T2Space (𝔸[K] ⊗[K] D) :=
  (coordsHomeomorph (Module.finBasis K D)).isEmbedding.t2Space

attribute [local instance] t2Space_adeleTensor

theorem continuous_rmat_adele : Continuous (rmat b 𝔸[K]) :=
  continuous_pi fun _ => continuous_pi fun l => (continuous_apply l).comp
    ((continuous_coords_adele b).comp (continuous_const.mul continuous_id))

theorem continuous_rmatUnits : Continuous (rmatUnits b 𝔸[K]) :=
  Units.continuous_iff.2 ⟨(continuous_rmat_adele b).comp Units.continuous_val,
    (continuous_rmat_adele b).comp Units.continuous_coe_inv⟩

theorem isCompact_preimage_rmatUnits {C : Set (GL (Fin d) 𝔸[K])} (hC : IsCompact C) :
    IsCompact (rmatUnits b 𝔸[K] ⁻¹' C) := by
  let ψ : Matrix (Fin d) (Fin d) 𝔸[K] → 𝔸[K] ⊗[K] D := fun A =>
    (coords b 𝔸[K]).symm (coords b 𝔸[K] 1 ᵥ* A)
  have hψ : Continuous ψ :=
    (continuous_coords_adele_symm b).comp (continuous_const.matrix_vecMul continuous_id)
  have hψr : ∀ w : 𝔸[K] ⊗[K] D, ψ (rmat b 𝔸[K] w) = w := by
    intro w
    simp only [ψ]
    rw [← coords_mul, one_mul, LinearEquiv.symm_apply_apply]
  let Fp : GL (Fin d) 𝔸[K] → (𝔸[K] ⊗[K] D) × (𝔸[K] ⊗[K] D)ᵐᵒᵖ := fun g =>
    (ψ (g : Matrix (Fin d) (Fin d) 𝔸[K]), MulOpposite.op (ψ (↑g⁻¹ : Matrix (Fin d) (Fin d) 𝔸[K])))
  have hFp : Continuous Fp := (hψ.comp Units.continuous_val).prodMk
    (MulOpposite.continuous_op.comp (hψ.comp Units.continuous_coe_inv))
  have hsub : rmatUnits b 𝔸[K] ⁻¹' C ⊆ Units.embedProduct _ ⁻¹' (Fp '' C) := by
    intro w hw
    refine ⟨_, hw, ?_⟩
    simp only [Fp, Units.embedProduct_apply]
    exact Prod.ext (hψr (w : 𝔸[K] ⊗[K] D)) (congrArg MulOpposite.op (hψr (↑w⁻¹ : 𝔸[K] ⊗[K] D)))
  have hcl : IsClosed (rmatUnits b 𝔸[K] ⁻¹' C) := hC.isClosed.preimage (continuous_rmatUnits b)
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.image hFp)).of_isClosed_subset
    hcl hsub

theorem exists_isCompact_normOneUnits :
    ∃ Ω : Set (𝔸[K] ⊗[K] D)ˣ, IsCompact Ω ∧ ∀ x ∈ normOneUnits b,
      ∃ δ : Dˣ, (rationalUnits K D δ)⁻¹ * x ∈ Ω := by
  obtain ⟨C, hC, h⟩ := exists_isCompact_rmatUnits b
  refine ⟨rmatUnits b 𝔸[K] ⁻¹' C, isCompact_preimage_rmatUnits b hC, fun x hx => ?_⟩
  obtain ⟨ξ, hξ⟩ := h x hx
  exact ⟨_, by rw [← rationalUnits'_eq]; exact hξ⟩

end Anisotropic

end

end GroundTheory.Automorphic
