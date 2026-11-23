import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv]
  [Algebra K.1 Ωv] [IsScalarTower K.1 Kv Ωv] [Algebra.IsIntegral Kv Ωv]

omit [Algebra.IsIntegral Kv Ωv] in

theorem globalDecomp_comp (ι : ℚ̄ →ₐ[K.1] Ωv) (g : K.1.fixingSubgroup) (σ : Gal(Ωv/Kv)) :
    globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ = g⁻¹ * globalDecomp Kv ι σ * g := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro y
  have h1 : ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ :
      ℚ̄ ≃ₐ[ℚ] ℚ̄) y)) = σ (ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y)) :=
    globalDecomp_apply Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ y
  have h2 := globalDecomp_apply Kv ι σ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y)
  have h3 : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) σ :
      ℚ̄ ≃ₐ[ℚ] ℚ̄) y) = (globalDecomp Kv ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) y) :=
    ι.injective (h1.trans h2.symm)
  change _ = ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ * (globalDecomp Kv ι σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) * (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)) y
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← h3, ← AlgEquiv.mul_apply, inv_mul_cancel,
    AlgEquiv.one_apply]

instance isDiscreteRep_res_globalDecomp (ι : ℚ̄ →ₐ[K.1] Ωv) :
    IsDiscreteRep (Rep.res (globalDecomp Kv ι) (unitsLimitRep K)) :=
  IsDiscreteRep.res (continuous_globalDecomp Kv ι) _

theorem unitsLocalRes_comp (ι : ℚ̄ →ₐ[K.1] Ωv) (g : K.1.fixingSubgroup) (n : ℕ) :
    unitsLocalRes Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n = unitsLocalRes Kv ι n := by
  have hconj := cohomologyMapAlong_conj (unitsLimitRep K) (continuous_globalDecomp Kv ι)
    (continuous_globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄))) g
    (globalDecomp_comp Kv ι g) n
  have e1 : unitsLocalRes Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)) n =
      cohomologyMapAlong (globalDecomp Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄)))
        (continuous_globalDecomp Kv _) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id
        (unitsLocalMor Kv (ι.comp (fixingSubgroupEquiv K.1 g : ℚ̄ →ₐ[K.1] ℚ̄))) n := by
    rw [unitsLocalRes, ← cohomologyMapAlong_comp]
    rfl
  have e2 : unitsLocalRes Kv ι n =
      cohomologyMapAlong (globalDecomp Kv ι) (continuous_globalDecomp Kv ι) (𝟙 _) n ≫
      cohomologyMapAlong (MonoidHom.id _) continuous_id (unitsLocalMor Kv ι) n := by
    rw [unitsLocalRes, ← cohomologyMapAlong_comp]
    rfl
  rw [e1, hconj, Category.assoc, ← cohomologyMapAlong_comp, e2]
  congr 1
  refine cohomologyMapAlong_congr _ _ _ _ rfl (fun a => ?_) n
  apply Additive.toMul.injective
  apply Units.ext
  change ι ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄))) =
    ι ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄)
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem unitsLocalRes_eq_of_algHom (ι ι' : ℚ̄ →ₐ[K.1] Ωv) (n : ℕ) :
    unitsLocalRes Kv ι' n = unitsLocalRes Kv ι n := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal ι ι'
  have : ι' = ι.comp (fixingSubgroupEquiv K.1 ((fixingSubgroupEquiv K.1).symm g) : ℚ̄ →ₐ[K.1] ℚ̄) := by
    rw [MulEquiv.apply_symm_apply]
    exact hg
  rw [this, unitsLocalRes_comp]

end

end GroundTheory.ProfCoh
