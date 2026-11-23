import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']

@[reducible] def bcF : C ⥤ CommAlgCat.{0} R' where
  obj T := CommAlgCat.of R' (R' ⊗[R] F.obj T)
  map φ := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ))
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_id F T b))
  map_comp φ ψ := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_comp F φ ψ b))

def bcM : BC F (bcF F R') where
  α T := (Algebra.TensorProduct.includeRight : F.obj T →ₐ[R] R' ⊗[R] F.obj T).toRingHom
  naturality _ _ := rfl
  smul T r b := by
    change (1 : R') ⊗ₜ[R] (r • b) = algebraMap R R' r • ((1 : R') ⊗ₜ[R] b)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  bij T := ⟨LinearEquiv.refl _ _, fun _ ↦ rfl⟩

variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')

def ev0 : M ⊗[R] C0 F →ₗ[R] ∀ T : C, R' ⊗[R] F.obj T :=
  LinearMap.pi fun T ↦ TensorProduct.map j (LinearMap.proj T)

def ev1 : M ⊗[R] C1 F →ₗ[R] ∀ (T T' : C) (_ : T ⟶ T'), R' ⊗[R] F.obj T' :=
  LinearMap.pi fun T ↦ LinearMap.pi fun T' ↦ LinearMap.pi fun φ ↦
    TensorProduct.map j ((LinearMap.proj φ) ∘ₗ (LinearMap.proj T') ∘ₗ (LinearMap.proj T))

theorem evaluation_zero_tmul (n : M) (g : C0 F) (T : C) : ev0 F j (n ⊗ₜ g) T = j n ⊗ₜ g T := rfl

theorem realTensorEvalAlgHom_tmul (n : M) (f : C1 F) {T T' : C} (φ : T ⟶ T') :
    ev1 F j (n ⊗ₜ f) T T' φ = j n ⊗ₜ f T T' φ := rfl

theorem evaluation_coboundary_zero_tensor (y : M ⊗[R] C0 F) :
    ev1 F j ((d0 F).lTensor M y) = d0 (bcF F R') (ev0 F j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n g =>
    funext T T' φ
    show ev1 F j (n ⊗ₜ d0 F g) T T' φ = ev0 F j (n ⊗ₜ g) T' - mp (bcF F R') φ (ev0 F j (n ⊗ₜ g) T)
    rw [realTensorEvalAlgHom_tmul, evaluation_zero_tmul, evaluation_zero_tmul, amitsur_d0_apply]
    show j n ⊗ₜ (g T' - mp F φ (g T)) =
      j n ⊗ₜ g T' - (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ)) (j n ⊗ₜ g T)
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.tmul_sub]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_cocycle (e : R' ⊗[R] H1 F ≃ₗ[R'] H1 (bcF F R'))
    (he : ∀ c, e (1 ⊗ₜ c) = (bcM F R').coef.pull1 c) (t : M ⊗[R] Z1 F) :
    ∃ z : Z1 (bcF F R'), z.1 = ev1 F j ((Z1 F).subtype.lTensor M t) ∧
      H1.mk (bcF F R') z = e (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul n c =>
    refine ⟨j n • (bcM F R').coef.pullbackOneCocycle c, ?_, ?_⟩
    · funext T T' φ
      show j n • ((1 : R') ⊗ₜ[R] (c.1 T T' φ)) = ev1 F j (n ⊗ₜ c.1) T T' φ
      rw [realTensorEvalAlgHom_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rw [map_smul, ← CoefMap.pullCohomologyOne_class]
      show j n • (bcM F R').coef.pull1 (H1.mk F c) = e (j n ⊗ₜ H1.mk F c)
      rw [← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨z1, h1, h1'⟩ := hx
    obtain ⟨z2, h2, h2'⟩ := hy
    refine ⟨z1 + z2, ?_, ?_⟩
    · simp only [Submodule.coe_add, h1, h2, map_add]
    · simp only [map_add, h1', h2']

theorem lTensor_iotaQ_injective_of_retract (h : H1CommutesBaseChange F) (p : R' →ₗ[R] M) (hp : p ∘ₗ j = LinearMap.id) :
    Function.Injective ((iotaQ F).lTensor M) := by
  obtain ⟨e, he⟩ := h R' (bcF F R') (bcM F R')
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective M (H1.mk_surjective F) x
  have hcomp : iotaQ F ∘ₗ H1.mk F = (LinearMap.range (d0 F)).mkQ ∘ₗ (Z1 F).subtype :=
    LinearMap.ext fun f => iotaQ_mk F f
  have hx' : ((LinearMap.range (d0 F)).mkQ).lTensor M ((Z1 F).subtype.lTensor M t) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, ← hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨y, hy⟩ := (lTensor_exact M (LinearMap.exact_map_mkQ_range (d0 F))
    (Submodule.mkQ_surjective _) ((Z1 F).subtype.lTensor M t)).1 hx'
  obtain ⟨z, hz1, hz2⟩ := exists_cocycle F j e he t
  have hz0 : H1.mk (bcF F R') z = 0 := by
    apply iotaQ_injective (bcF F R')
    rw [iotaQ_mk, map_zero, Submodule.Quotient.mk_eq_zero, hz1, ← hy, evaluation_coboundary_zero_tensor]
    exact LinearMap.mem_range_self _ _
  have hx0 : j.rTensor (H1 F) ((H1.mk F).lTensor M t) = 0 := by
    rw [← e.map_eq_zero_iff, ← hz2, hz0]
  calc (H1.mk F).lTensor M t = (p ∘ₗ j).rTensor (H1 F) ((H1.mk F).lTensor M t) := by
        rw [hp, LinearMap.rTensor_id_apply]
    _ = p.rTensor (H1 F) (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := LinearMap.rTensor_comp_apply _ _ _ _
    _ = 0 := by rw [hx0, map_zero]

end BaseChange

theorem iotaQ_lTensor_injective (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (h : H1CommutesBaseChange F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective ((iotaQ F).lTensor M) := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  exact lTensor_iotaQ_injective_of_retract F (TrivSqZeroExt.inrHom R M) h (TrivSqZeroExt.sndHom R M)
    (LinearMap.ext fun m => by simp)

end GlobalTheory.CompanionTheory.WedgeOf
