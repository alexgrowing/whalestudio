import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

private theorem of_section {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞] (W : MorphismProperty 𝒞) [W.IsStableUnderBaseChange]
    {Y X P P' Z B V : 𝒞} (pk : P ⟶ Y) (pk' : P' ⟶ X) (j : X ⟶ Y) (pw : P' ⟶ P) (hp : IsPullback pw pk' pk j)
    (ε : Y ⟶ P) (hε : ε ≫ pk = 𝟙 Y) (sY : Y ⟶ B) (g : V ⟶ B) (sX : X ⟶ V) (ov : j ≫ sY = sX ≫ g)
    (e : Z ≅ P') (q : Z ⟶ V) (hq : e.hom ≫ pk' ≫ sX = q) (h : (e.hom ≫ pw) ≫ pk ≫ sY = q ≫ g)
    (hF : W (pullback.lift (e.hom ≫ pw) q h)) : W (pullback.lift j sX ov) := by
  have hε' : (j ≫ ε) ≫ pk = 𝟙 X ≫ j := by simp [hε]
  let ε₀ : X ⟶ P' := hp.lift (j ≫ ε) (𝟙 X) hε'
  have h₁ : ε₀ ≫ pw = j ≫ ε := hp.lift_fst _ _ _
  have h₂ : ε₀ ≫ pk' = 𝟙 X := hp.lift_snd _ _ _
  have hE : (pullback.fst sY g ≫ ε) ≫ pk ≫ sY = pullback.snd sY g ≫ g := by
    rw [Category.assoc, reassoc_of% hε, pullback.condition]
  let εE : pullback sY g ⟶ pullback (pk ≫ sY) g := pullback.lift (pullback.fst sY g ≫ ε) (pullback.snd sY g) hE
  have F₁ : pullback.lift (e.hom ≫ pw) q h ≫ pullback.fst _ _ = e.hom ≫ pw := pullback.lift_fst _ _ _
  have F₂ : pullback.lift (e.hom ≫ pw) q h ≫ pullback.snd _ _ = q := pullback.lift_snd _ _ _
  have f₁ : pullback.lift j sX ov ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have f₂ : pullback.lift j sX ov ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  have E₁ : εE ≫ pullback.fst _ _ = pullback.fst sY g ≫ ε := pullback.lift_fst _ _ _
  have E₂ : εE ≫ pullback.snd _ _ = pullback.snd sY g := pullback.lift_snd _ _ _
  have sq : IsPullback (ε₀ ≫ e.inv) (pullback.lift j sX ov) (pullback.lift (e.hom ≫ pw) q h) εE := by
    have hcomm : (ε₀ ≫ e.inv) ≫ pullback.lift (e.hom ≫ pw) q h = pullback.lift j sX ov ≫ εE := by
      apply pullback.hom_ext
      · simp only [Category.assoc, F₁, E₁, Iso.inv_hom_id_assoc, h₁]
        rw [reassoc_of% f₁]
      · simp only [Category.assoc, F₂, E₂, f₂]
        rw [← hq, Iso.inv_hom_id_assoc, reassoc_of% h₂]
    refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ e.hom ≫ pk') ?_ ?_ ?_⟩⟩
    · intro s
      have c := s.condition
      have c₁ : s.fst ≫ e.hom ≫ pw = s.snd ≫ pullback.fst sY g ≫ ε := by
        simpa only [Category.assoc, F₁, E₁] using c =≫ pullback.fst _ _
      have c₃ : s.fst ≫ e.hom ≫ pk' ≫ j = s.snd ≫ pullback.fst sY g := by
        have := c₁ =≫ pk
        simpa only [Category.assoc, hp.w, hε, Category.comp_id] using this
      have key : (s.fst ≫ e.hom ≫ pk') ≫ ε₀ = s.fst ≫ e.hom := by
        apply hp.hom_ext
        · simp only [Category.assoc, h₁]
          rw [reassoc_of% c₃, c₁]
        · simp only [Category.assoc, h₂, Category.comp_id]
      rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro s
      have c := s.condition
      have c₁ : s.fst ≫ e.hom ≫ pw = s.snd ≫ pullback.fst sY g ≫ ε := by
        simpa only [Category.assoc, F₁, E₁] using c =≫ pullback.fst _ _
      have c₂ : s.fst ≫ q = s.snd ≫ pullback.snd sY g := by
        simpa only [Category.assoc, F₂, E₂] using c =≫ pullback.snd _ _
      have c₃ : s.fst ≫ e.hom ≫ pk' ≫ j = s.snd ≫ pullback.fst sY g := by
        have := c₁ =≫ pk
        simpa only [Category.assoc, hp.w, hε, Category.comp_id] using this
      apply pullback.hom_ext
      · simpa only [Category.assoc, f₁] using c₃
      · simp only [Category.assoc, f₂]
        rw [hq]; exact c₂
    · intro s m h₃ _
      have := h₃ =≫ (e.hom ≫ pk')
      simp only [Category.assoc, Iso.inv_hom_id_assoc, h₂, Category.comp_id] at this
      exact this
  exact MorphismProperty.of_isPullback sq hF

theorem baseFet_holds : PowCart → PiFet → BaseFet := by
  intro hPow hPi p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T M c a hN C
  obtain ⟨e, hfin, het⟩ := hPi p D G L E gb w q r 𝔴 𝔫 S k T M c a hN C
  have hp : IsPullback (C.pw k) (GlobalTheory.KS.pow (T.M M).univ.A k).hom (GlobalTheory.KS.pow S.Y.univ.A k).hom C.j :=
    ((hPow _ _ _ _ _ _ C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1)
  let ε : S.Y.X ⟶ (GlobalTheory.KS.pow S.Y.univ.A k).left :=
    (Pi.lift (fun _ : Fin k => (1 : 𝟙_ (Over S.Y.X) ⟶ S.Y.univ.A))).left
  have hε : ε ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = 𝟙 _ := Over.w (Pi.lift (fun _ : Fin k => (1 : 𝟙_ (Over S.Y.X) ⟶ S.Y.univ.A)))
  have key : ∀ (W : MorphismProperty Scheme.{0}) [W.IsStableUnderBaseChange],
      W (pullback.lift (S.pi T C) (T.X.q _) e) → W (pullback.lift C.j (T.M M).s C.ov) := fun W _ hF =>
    of_section W _ _ C.j (C.pw k) hp ε hε S.Y.s (gen (Ow w) E) (T.M M).s C.ov (T.e M) _ (T.e_q M) e hF
  exact ⟨key @IsFinite hfin, key @Etale het⟩

end UpperTheory.Gal.FiniteEtaleModels
