import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem eq_of_comp_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let f' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f
  let g' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk g h.symm
  haveI : IsSeparated (Over.mk s).hom := ‹IsSeparated s›
  let d' : Over.mk (d ≫ f ≫ s) ⟶ Over.mk (f ≫ s) := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := Over.OverMorphism.ext hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  exact congrArg CommaMorphism.left ((cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g'))

theorem schemeDominant_spec_of_injective {A B : Type} [CommRing A] [CommRing B] [_root_.IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem act_comm_of_torsion : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  intro hL h₂ E _ _ _ H R _ _ _ S s B B₀ ρ ρ₀ ψ hψ hw C _ _ _ _ n hn x h
  letI := H.starRing
  obtain ⟨ρ', hρ'⟩ := polOActPull _ _ s B₀ B ψ hψ hw.symm (𝓞 E) ρ₀
  obtain ⟨P, g, hg, -, hm, ht⟩ := hL.polBaseChange _ _ (TF (R := R) C).hom B
  have gp : IsGrpPullback P.A B.A (TF (R := R) C).hom g := ⟨hg, fun T a b a₀ b₀ ha hb => by
    have e₁ : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
    have e₂ : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
    rw [e₁, e₂, ← hm]; rfl⟩
  obtain ⟨σ, hσ⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ
  obtain ⟨σ', hσ'⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ'
  obtain ⟨c, hc⟩ := exists_starNormLE_of_isCMField E (fun a => H.bar_eq a) x
  set j := 4 ^ P.g * P.g.factorial * (2 * c) with hj
  have hlt : j < (n ^ j) ^ 2 := (Nat.lt_pow_self hn).trans_le (Nat.le_self_pow two_ne_zero _)
  have key := h₂ P.g c (n ^ j) hlt C (Nat.cast_ne_zero.2 (by positivity)) P P rfl rfl (Iso.refl _)
    (ThetaPtDet.isPolIso_refl P) _ σ σ' x hc fun y hy => by
      let u : TF (R := R) C ⟶ Over.mk ((baseOver (Sp C)).hom ≫ (TF (R := R) C).hom) :=
        Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
      let z : TF (R := R) C ⟶ B.A := u ≫ pushHom gp _ y
      have hz : z.left = y.left ≫ g := Category.id_comp _
      have hz' : z ^ n ^ j = 1 := by
        rw [← MonObj.comp_pow, ← map_pow, hy, map_one, MonObj.comp_one]
      have e := h j z hz'
      rw [← hρ', ← Category.assoc, ← Over.comp_left] at e
      have e' : (z ≫ ρ.act x).left = (z ≫ ρ'.act x).left := hψ.1.hom_ext e (by rw [Over.w, Over.w])
      rw [Iso.refl_hom, Category.comp_id, Category.id_comp]
      refine Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))
      rw [Over.comp_left _ _ _ z, Over.comp_left _ _ _ z, hz] at e'
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hσ, hσ']
      simpa only [Category.assoc] using e'
  rw [Iso.refl_hom, Category.comp_id, Category.id_comp] at key
  haveI : IsSchemeTheoreticallyDominant (jK R) := schemeDominant_spec_of_injective _ (IsFractionRing.injective R _)
  haveI : IsSchemeTheoreticallyDominant (jFK (R := R) C) := schemeDominant_spec_of_injective _ (RingHom.injective _)
  haveI : IsSchemeTheoreticallyDominant (TF (R := R) C).hom := by
    show IsSchemeTheoreticallyDominant (_ ≫ _); infer_instance
  haveI := B.isAb.proper
  haveI := B.isAb.smooth
  haveI : QuasiCompact (TF (R := R) C).hom := by
    show QuasiCompact (spMap (algebraMap (FractionRing R) C) ≫ spMap (algebraMap R (FractionRing R))); infer_instance
  haveI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  rw [← hρ', eq_of_comp_schemeDominant B.A.hom ((Over.w (ρ.act x)).trans (Over.w (ρ'.act x)).symm) g
    (by rw [← hσ, ← hσ', key])]

end GlobalTheory.Ex.Trait
