import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ValEmb

theorem valAt_pull {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (j : X ⟶ Spec (CommRingCat.of A)) (x : Spec (CommRingCat.of B) ⟶ X) (ρ : A →+* B)
    (h : x ≫ j = Spec.map (CommRingCat.ofHom ρ)) (f : A) :
    valAt x ⊤ le_top (j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)) = ρ f := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop ≫ x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      = CommRingCat.ofHom ρ := by
    have : j.appTop ≫ x.appTop = (Spec.map (CommRingCat.ofHom ρ)).appTop := by
      rw [← h, Scheme.Hom.comp_appTop]
    rw [reassoc_of% this, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have h2 := congrArg (fun φ => φ.hom f) h1
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]
  simpa using h2

theorem valAt_sub {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem val_emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  intro R _ _ T _ _ Γ j hj f s hs B _ y ρ hy
  have hz : s - j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f) = 0 := by
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ _ fun t h => ?_
    rw [valAt_sub, hs t, valAt_pull j (Γ.pt t).left _ (hj.pt t) f]
    simp
  rw [sub_eq_zero.mp hz]
  exact valAt_pull j y ρ hy f

end GlobalTheory.CompanionTheory.Ar.BT.ValEmb
