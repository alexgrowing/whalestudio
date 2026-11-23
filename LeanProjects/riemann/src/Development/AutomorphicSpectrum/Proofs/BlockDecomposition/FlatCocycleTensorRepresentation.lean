import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_coords_bijective {R : Type} [CommRing R] {I : Type} [Finite I] {P : Type}
    [AddCommGroup P] [Module R P] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (e : P ≃ₗ[R] ∀ i, M i) (N : Type) [AddCommGroup N] [Module R N] :
    Function.Bijective (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) := by
  classical
  cases nonempty_fintype I
  have hcomp : (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) =
      (TensorProduct.piLeft (R := R) (N := N) (M := M)).toLinearMap ∘ₗ
        (LinearEquiv.rTensor N e).toLinearMap := by
    apply TensorProduct.ext'
    intro p n
    funext i
    simp
  rw [hcomp]
  exact ((LinearEquiv.rTensor N e).trans
    (TensorProduct.piLeft (R := R) (N := N) (M := M))).bijective

section Cochains

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ a : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj a.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def twoCochainsPiComposableEquiv : C2 F ≃ₗ[R]
    ∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  invFun g T T' T'' φ ψ := g ⟨T, T', T'', φ, ψ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def evC {T T' : C} (φ : T ⟶ T') : C1 F →ₗ[R] F.obj T' where
  toFun f := f T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_comp_coboundary_one {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (LinearMap.proj (⟨T, T', T'', φ, ψ⟩ : Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')) :
        (∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1) →ₗ[R] _) ∘ₗ
      (twoCochainsPiComposableEquiv F).toLinearMap ∘ₗ d1 F =
    (mp F ψ).toLinearMap ∘ₗ evC F φ - evC F (φ ≫ ψ) + evC F ψ := by
  ext f
  rfl

end Cochains

theorem cocycle_of_flat (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C]
    [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] N)
    (hf : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f T T'' (φ ≫ ψ) = (mp F ψ).toLinearMap.rTensor N (f T T' φ) + f T' T'' ψ) :
    ∃ t : Z1 F ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = f T T' φ := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ => Finite.of_subsingleton
  have b1 := rTensor_coords_bijective (R := R) _ (oneCochainsPiArrowsEquiv F) N
  have b2 := rTensor_coords_bijective (R := R) _ (twoCochainsPiComposableEquiv F) N
  obtain ⟨v, hv⟩ := b1.2 (fun a => f a.1 a.2.1 a.2.2)
  have hv' : ∀ (T T' : C) (φ : T ⟶ T'), (evC F φ).rTensor N v = f T T' φ := fun T T' φ =>
    congrFun hv ⟨T, T', φ⟩
  have hw : (d1 F).rTensor N v = 0 := by
    apply b2.1
    rw [map_zero]
    funext ⟨T, T', T'', φ, ψ⟩
    have h := congrArg (fun g => LinearMap.rTensor N g v) (evaluation_comp_coboundary_one F φ ψ)
    simp only [LinearMap.rTensor_add, LinearMap.rTensor_sub, LinearMap.rTensor_comp,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hv'] at h
    rw [hf T T' T'' φ ψ] at h
    simp only [LinearMap.pi_apply, Pi.zero_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [h]
    abel
  have hex : Function.Exact (Z1 F).subtype (d1 F) := fun x => by
    rw [← LinearMap.mem_ker, ← commAlgFunctorCocyclesOne_eq_ker]
    simp
  obtain ⟨t, ht⟩ := (Module.Flat.rTensor_exact N hex v).1 hw
  refine ⟨t, fun T T' φ => ?_⟩
  have : evZ F φ = evC F φ ∘ₗ (Z1 F).subtype := rfl
  rw [this, LinearMap.rTensor_comp, LinearMap.comp_apply, ht, hv']

end GlobalTheory.CompanionTheory.Axis
