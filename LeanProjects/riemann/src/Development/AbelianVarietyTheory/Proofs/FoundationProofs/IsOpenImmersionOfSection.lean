import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

namespace GlobalTheory.FlatLine.DefinitePoint

theorem subsingleton_of_etale {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Sp K) [Etale f] {Z : Set X}
    (hZ : IsIrreducible Z) : Z.Subsingleton := by
  have : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  obtain ⟨o⟩ : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  have hd := f.isDiscrete_preimage_singleton o
  have hu : f ⁻¹' {o} = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum K) _ _
  have : DiscreteTopology X := isDiscrete_univ_iff.mp (hu ▸ hd)
  exact hZ.isPreirreducible.subsingleton

theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 _) :
    IsOpenImmersion s := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
    (inferInstanceAs (IsOpenImmersion (Limits.pullback.diagonal f))) (by rw [hs]; infer_instance)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etale_strK (Xo : Moduli Dw l) (c : Coeff l) (hq : Dw.q = 0) : Etale (strK (Xo := Xo) (c := c)) := by
  have h0 : Dw.dim = 0 := by rw [Datum.dim, hq, mul_zero]
  have hs : SmoothOfRelativeDimension 0 Xo.s := h0 ▸ Xo.smooth
  have he : Etale Xo.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  infer_instance

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

theorem isAlgebraic_kap (Z : Comp Xo c) (hZ : (Z : Set (Xo.XF c)).Subsingleton) :
    Algebra.IsAlgebraic c.F (kap Z) := by
  obtain ⟨L, _, _, j, g, hg, hgZ⟩ := exists_numberField_point Z
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L (Xo.XF c)).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hg hgZ
  have hp : p = genPt Z := by
    refine hZ ?_ (CompSplitPfB.cspB_genPt_mem Z)
    obtain ⟨o⟩ : Nonempty (Sp L) := ⟨IsLocalRing.closedPoint L⟩
    have := hgZ o
    rwa [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at this
  subst hp
  have : CharZero (kap Z) := charZero_of_injective_algebraMap (algebraMap c.F (kap Z)).injective
  have ha : Algebra.IsAlgebraic ℚ (kap Z) :=
    Algebra.IsAlgebraic.of_injective (φ.hom.toRatAlgHom) φ.hom.injective
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → FnAlgClosed Xo c → ∀ Z : Comp Xo c, ∃ y₀ : FrPt Xo c c.F, LiesOn Z y₀ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x := by
  intro E _ _ _ H Dw l Xo c hq hac Z
  have := etale_strK Xo c hq
  have hZ := subsingleton_of_etale (strK (Xo := Xo) (c := c)) (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c)))
  have halg := isAlgebraic_kap Z hZ
  have hsurj : Function.Surjective (algebraMap c.F (kap Z)) := fun a => by
    obtain ⟨b, hb⟩ := hac Z (algebraMap (kap Z) (Om Z) a) ((halg.isAlgebraic a).algebraMap)
    refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
    rw [← hb, ← IsScalarTower.algebraMap_apply]
  let e : c.F ≃+* kap Z := RingEquiv.ofBijective _ ⟨(algebraMap c.F (kap Z)).injective, hsurj⟩
  let g₀ : Sp c.F ⟶ Xo.XF c := spMap e.symm.toRingHom ≫ genSp Z
  have hg₀ : g₀ ≫ strK = spMap (algebraMap c.F c.F) := by
    rw [Category.assoc, genSp_strK, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x => e.symm_apply_apply x)
  have hid : spMap (algebraMap c.F c.F) = 𝟙 _ := Spec.map_id _
  have hpt : ∀ s, g₀ s = genPt Z := fun s => by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have := isOpenImmersion_of_section strK g₀ (hg₀.trans hid)
  obtain ⟨y₀, hy₀⟩ := exists_frPt_local (c := c) GlobalTheory.abelianSchemeLaws_all.2.secTwist _ (prX_over hg₀)
  refine ⟨y₀, fun s => ?_, fun S _ _ y hy => ?_⟩
  · rw [ptF_eq hg₀ hy₀, hpt]
    exact CompSplitPfB.cspB_genPt_mem Z
  · have hr : Set.range (ptF y) ⊆ Set.range g₀ := by
      rintro _ ⟨s, rfl⟩
      exact ⟨IsLocalRing.closedPoint c.F, (hpt _).trans (hZ (CompSplitPfB.cspB_genPt_mem Z) (hy s))⟩
    have h1 := IsOpenImmersion.lift_fac g₀ (ptF y) hr
    have h2 : IsOpenImmersion.lift g₀ (ptF y) hr = spMap (algebraMap c.F S) := by
      have h3 := congrArg (· ≫ strK) h1
      simp only [Category.assoc, hg₀, hid, Category.comp_id] at h3
      rw [h3, ptF, Limits.pullback.lift_snd]
    rw [hy₀, ← Category.assoc, ← h2, h1, ptF, Limits.pullback.lift_fst]

end GlobalTheory.FlatLine.DefinitePoint
