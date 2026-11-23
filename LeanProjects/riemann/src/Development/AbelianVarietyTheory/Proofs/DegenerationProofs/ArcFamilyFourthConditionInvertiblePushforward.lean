import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcAbelianLocusAndModuliOfTraitDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcDataStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiserStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcClause

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_lift (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : V →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap V.subtype := by
    rw [Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F, PrimeSpectrum.comap g default = PrimeSpectrum.comap V.subtype q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact Subtype.ext h1
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap V.subtype = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap V.subtype) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap V.subtype)).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap V.subtype)) (default : PrimeSpectrum K) = z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

theorem not_mem_generic {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (f : R →+* R') {r : R} (hr : f r ≠ 0)
    (p : PrimeSpectrum (FractionRing R')) : r ∉ ((jK R' ≫ spMap f) p).asIdeal := by
  intro h
  have h1 : algebraMap R' (FractionRing R') (f r) ∈ PrimeSpectrum.asIdeal p := h
  rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal p)] at h1
  exact hr (IsFractionRing.injective R' (FractionRing R') (h1.trans (map_zero _).symm))

theorem arc_clause : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hX hF E _ _ _ H D l Xo c W₀ Y p hN hA O' _ _ _ b ϖ a hB
  obtain ⟨m, Z, π, t, mt, hodd, hunit, hfin, hsurj, hAF⟩ := hA
  have hm : IsUnit (m : O') := by simpa using hunit.map b
  obtain ⟨R₁, _, _, g, y₁, hg, hgf, hR, hTD, hθ, hf⟩ := hF E H D l Xo c W₀ Y O' b ϖ a hB m hodd hm
  let gam : FractionRing (PowerSeries O') →+* FractionRing R₁ :=
    IsFractionRing.lift (g := (algebraMap R₁ (FractionRing R₁)).comp g) ((IsFractionRing.injective R₁ _).comp hg)
  have hgam : ∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r) := fun r =>
    IsFractionRing.lift_algebraMap _ r
  obtain ⟨y, hy, hTy⟩ := GlobalTheory.T.arcGenericPoint_descends_to_powerSeries h1 h2 h3 h4 h5 h6 E H D l Xo c W₀ Y O' b a ϖ hB R₁ g y₁ gam hgam hgf hR hTD
  have hys : y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have := hTy.1
    rwa [show spMap (RingHom.id (PowerSeries O')) = 𝟙 _ from Spec.map_id _, Category.id_comp] at this
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.arc_generic_point_extends_powerSeries h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB m Z π t mt hfin hsurj hAF R₁ g y₁ gam hgam hgf hR
    y hy hys hθ hf
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB y χ hχ hTy
  have c4 := GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData h1 h2 h3 h4 h5 h6 hE hU hP hX E H D l Xo c W₀ Y O' b a ϖ hB hN.2.2.1 y χ hχ hTy
  have hϖ : ϖ ≠ 0 := by
    rcases hB with ⟨-, rfl⟩ | ⟨-, h, -⟩
    exacts [one_ne_zero, h.ne_zero]
  refine ⟨χ, fun χ' => ⟨fun h => h ▸ ⟨c1, c2, c3, c4⟩, fun ⟨d1, _, d3, d4⟩ => ?_⟩, fun hirr y' ev hs hr hd hC hXv => ?_⟩
  · have hpid : IsPrincipalIdealRing O' ∧ IsLocalRing O' := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · letI := h.toField
        exact ⟨inferInstance, inferInstance⟩
      · exact ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hpid
    have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (f := PowerSeries.C (R := O')) PowerSeries.C_injective
    obtain ⟨y', hy'⟩ := exists_lift (c.V W₀) Y (jK (PowerSeries O') ≫ χ') (by
      rintro _ ⟨q, rfl⟩
      refine d3 _ ?_
      have := not_mem_generic (RingHom.id (PowerSeries O')) (r := PowerSeries.C ϖ * PowerSeries.X)
        (mul_ne_zero (fun h => hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero) q
      exact this)
    exact GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a (PowerSeries O') (Ideal.span {PowerSeries.X})
      (PowerSeries.C (R := O')) PowerSeries.X ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
      (fun h => PowerSeries.X_prime.not_unit (Ideal.span_singleton_eq_top.1 h)) PowerSeries.C_injective
      χ' χ y' y hy' hχ.symm d1 c1 d4 c4
  · rcases hB with ⟨-, rfl⟩ | ⟨hdvr, -, hc⟩
    · exact absurd isUnit_one hirr.not_isUnit
    have hc' : IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
      rwa [hirr.maximalIdeal_eq]
    have hrg : Set.range (jK O' ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
      rintro _ ⟨q, rfl⟩
      refine c3 _ ?_
      have := not_mem_generic ev (r := PowerSeries.C ϖ * PowerSeries.X)
        (by rw [map_mul, hC, hXv]; exact mul_ne_zero hϖ hϖ) q
      exact this
    have c5 := GlobalTheory.T.arcData_specialise_at_uniformiser h1 h2 hT h4.unifBaseChange h5 E H D l Xo c _ _ Y O' b ϖ a hirr hc' ev hC hXv χ c1 hrg c4
    obtain ⟨z, hz⟩ := exists_lift (c.V W₀) Y _ hrg
    obtain ⟨z', hz'⟩ := exists_lift (c.V W₀) Y _ hr
    have hid : spMap (RingHom.id O') = 𝟙 _ := Spec.map_id _
    have hev : spMap ev ≫ spMap (PowerSeries.C (R := O')) = spMap (RingHom.id O') := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact hC x
    refine GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a O' (Ideal.span {ϖ}) (RingHom.id O') ϖ
      ⟨inferInstance, inferInstance, inferInstance, hc⟩
      (fun h => hirr.not_isUnit (Ideal.span_singleton_eq_top.1 h)) Function.injective_id
      _ y' z z' hz hz' ?_ ?_ c5 hd
    · rw [Category.assoc, c1, ← Category.assoc, hev]
    · rw [hid, Category.id_comp, hs]

end GlobalTheory.LN.ArcClause
