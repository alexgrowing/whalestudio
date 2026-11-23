import Mathlib
import GroundTheory.TateCohomology.Induced
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Criterion

variable (M : Rep.{u} k G)

noncomputable def toCoindRes :
    M ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) :=
  ofHom ⟨LinearMap.codRestrict _ (LinearMap.pi fun x : G => M.ρ x) fun m => by
      rw [Representation.mem_coindV]
      intro s x
      simp [map_mul],
    fun g => LinearMap.ext fun m => by
      apply Subtype.ext
      funext x
      change M.ρ x (M.ρ g m) = M.ρ (x * g) m
      rw [map_mul, Module.End.mul_apply]⟩

noncomputable def fromCoindRes (φ : M.V →ₗ[k] M.V) :
    coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) ⟶ M :=
  ofHom ⟨∑ x : G, M.ρ x⁻¹ ∘ₗ φ ∘ₗ LinearMap.proj x ∘ₗ
      (Representation.coindV (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M).ρ).subtype,
    fun g => LinearMap.ext fun f => by
      simp only [LinearMap.coe_comp, LinearMap.coe_sum, Function.comp_apply, Finset.sum_apply,
        map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun x => ?_
      change M.ρ x⁻¹ (φ (f.1 (x * g))) = M.ρ g (M.ρ (x * g)⁻¹ (φ (f.1 (x * g))))
      rw [← Module.End.mul_apply (M.ρ g) (M.ρ (x * g)⁻¹), ← map_mul, mul_inv_rev,
        mul_inv_cancel_left]⟩

theorem toCoindRes_fromCoindRes (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    toCoindRes M ≫ fromCoindRes M φ = 𝟙 M := by
  ext m
  change (fromCoindRes M φ).hom.toLinearMap ((toCoindRes M).hom.toLinearMap m) = m
  refine (LinearMap.sum_apply _ _ _).trans ?_
  change ∑ x : G, M.ρ x⁻¹ (φ (M.ρ x m)) = m
  conv_rhs => rw [← hφ m]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp

theorem tateAcyclic_of_sum_eq (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : TateAcyclic M :=
  (tateAcyclic_coind_bot _).of_retract _ _ (toCoindRes_fromCoindRes M φ hφ)

end Criterion

section Tensor

omit [Fintype G] in

noncomputable def coeffOneProj : MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G :=
  MonoidAlgebra.lsingle 1 ∘ₗ Finsupp.lapply 1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

omit [Fintype G] in

theorem coeffOneProj_apply (x : MonoidAlgebra k G) :
    coeffOneProj x = MonoidAlgebra.single 1 (x.coeff 1) := rfl

variable (B : Rep.{u} k G)

theorem sum_leftRegular_tensor (t : (leftRegular k G ⊗ B : Rep k G)) :
    ∑ g : G, (leftRegular k G ⊗ B).ρ g
      (TensorProduct.map coeffOneProj LinearMap.id ((leftRegular k G ⊗ B).ρ g⁻¹ t)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | tmul x b =>
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib, hx, hy]
    | single h c =>
      rw [Fintype.sum_eq_single h]
      · simp [Rep.tensor_ρ, coeffOneProj_apply]
      · intro g hg
        have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
        simp [Rep.tensor_ρ, coeffOneProj_apply, this]

theorem tateAcyclic_leftRegular_tensor : TateAcyclic (leftRegular k G ⊗ B) :=
  tateAcyclic_of_sum_eq _ (TensorProduct.map coeffOneProj LinearMap.id) (sum_leftRegular_tensor B)

theorem tateAcyclic_leftRegular_tensor_trivial (V : Type u) [AddCommGroup V] [Module k V] :
    TateAcyclic (leftRegular k G ⊗ trivial k G V) :=
  tateAcyclic_leftRegular_tensor _

theorem tateAcyclic_leftRegular : TateAcyclic (leftRegular k G) :=
  (tateAcyclic_leftRegular_tensor (𝟙_ (Rep k G))).of_iso (ρ_ (leftRegular k G)).symm

theorem tateAcyclic_free (α : Type u) : TateAcyclic (free k G α) := by
  classical
  exact (tateAcyclic_leftRegular_tensor_trivial _).of_iso (leftRegularTensorTrivialIsoFree k G α).symm

end Tensor

section Free

variable (M : Rep.{u} k G)

end Free

end GroundTheory.GroupCoh
