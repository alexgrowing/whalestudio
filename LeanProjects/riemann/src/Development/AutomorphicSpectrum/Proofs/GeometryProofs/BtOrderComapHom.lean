import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.Funct

theorem valAt_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (a : X ⟶ Y)
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : x ≫ a = y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ U)) (s : Γ(Y, U)) :
    valAt x (a ⁻¹ᵁ U) h' ((a.app U).hom s) = valAt y U h s := by
  subst hy
  simp only [valAt]
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem regularAt_pullback {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ₁ : QFGroup R T)
    {T' : Type} [CommGroup T'] (Γ₂ : QFGroup R T') (a : Γ₁.G ⟶ Γ₂.G) (α : T →* T')
    (ha : ∀ t, Γ₁.pt t ≫ a = Γ₂.pt (α t)) (φ : T' → FractionRing R) (g : Γ₁.G.left)
    (hg : Γ₂.RegularAt φ (a.left g)) : Γ₁.RegularAt (fun t => φ (α t)) g := by
  obtain ⟨U, hU, s, hs⟩ := hg
  refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun t h => ?_⟩
  have hy : (Γ₁.pt t).left ≫ a.left = (Γ₂.pt (α t)).left := by
    rw [← ha t, Over.comp_left]
  have h₂ : ⊤ ≤ (Γ₂.pt (α t)).left ⁻¹ᵁ U := by
    rw [← hy]
    exact h
  rw [valAt_pullback _ _ _ hy U h₂ h s]
  exact hs (α t) h₂

theorem comp_mem_btOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    have h := regularAt_pullback Γ Γ' a α ha _ g (hf (α t) (a.left g) trivial)
    change Γ.RegularAt (fun x => algebraMap R (FractionRing R) (f (α (t * x)))) g
    simpa only [map_mul] using h
  exact hle hf

end GlobalTheory.CompanionTheory.Ar.BT.Funct
