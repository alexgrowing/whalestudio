import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlagStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagBundle

theorem exists_spMap_fromSpecResidueField {Z : Scheme.{0}} (y : Z) {K : Type} [Field K] (p : Sp K ⟶ Z)
    (hp : p (IsLocalRing.closedPoint K) = y) :
    ∃ σ : Z.residueField y →+* K, spMap σ ≫ Z.fromSpecResidueField y = p := by
  subst hp
  exact ⟨(Z.descResidueField (Scheme.stalkClosedPointTo p)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z p⟩

theorem coBear_swap {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
    {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}
    {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ : Sp K ⟶ Y₁.X} {p₂ : Sp K ⟶ Y₂.X}
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) (hx : x = x') : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂ p₁ := by
  subst hx
  obtain ⟨A, hA, g, hg, h₁, h₂⟩ := h
  exact ⟨A, hA, g, hg, h₂, h₁⟩

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.conclusion : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ r hr hrc K _ p p' hp hpp' hc
  set y₁ := r (IsLocalRing.closedPoint Y₂.Fn)
  let c : Sp (Y₁.X.residueField y₁) ⟶ Y₁.X := Y₁.X.fromSpecResidueField y₁
  obtain ⟨τ, hτ⟩ := exists_spMap_fromSpecResidueField y₁ r rfl
  obtain ⟨σ, hσ⟩ := exists_spMap_fromSpecResidueField y₁ p hp
  obtain ⟨A, hA, g, hg, hb₁⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ hR₁ _ c
  obtain ⟨s, ⟨hs, hb₂⟩, -⟩ := hR₂.2.2 _ (c ≫ f₁) A hA g hg
  have hcs : CoBear Eb S₁ φ₁ S₂ φ₂ (c ≫ f₁) c s := ⟨A, hA, g, hg, hb₁, hb₂⟩
  have hτc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ τ _ _ _ hcs
  have hσc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ _ _ σ _ _ _ hcs
  have hτ' : spMap τ ≫ c = r := hτ
  have hσ' : spMap σ ≫ c = p := hσ
  rw [hτ'] at hτc
  rw [hσ'] at hσc
  have e₁ : (spMap τ ≫ s) ≫ f₂ = r ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hτ']
  have e₂ : (spMap σ ≫ s) ≫ f₂ = p ≫ f₁ := by rw [Category.assoc, hs, ← Category.assoc, hσ']
  have k₁ : spMap τ ≫ s = (ratOf Y₂).pt :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ r e₁ hr.symm
      (coBear_swap hτc (by rw [Category.assoc, hs])) (coBear_swap hrc hr)
  have k₂ : p' = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ _ _ _ p hpp'.symm e₂
      (coBear_swap hc hpp') (coBear_swap hσc (by rw [Category.assoc, hs]))
  have hgen : s (IsLocalRing.closedPoint _) = genericPoint Y₂.X := by
    have e : (spMap τ ≫ s) (IsLocalRing.closedPoint Y₂.Fn) = s (IsLocalRing.closedPoint _) := by
      exact (Scheme.Hom.comp_apply _ _ _).trans
        (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
    rw [← e, k₁]
    exact Scheme.fromSpecStalk_closedPoint
  rw [k₂, ← hgen]
  exact (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg s (Subsingleton.elim (α := PrimeSpectrum (Y₁.X.residueField y₁)) _ _))
