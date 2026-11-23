import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.IntegralModelFacts

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] (β : O →+* F) (hβ : Function.Injective β)
    (x : Sp O) : x ∈ Set.range (spMap β) ↔ ∀ o : O, o ≠ 0 → o ∉ x.asIdeal := by
  constructor
  · rintro ⟨y, rfl⟩ o ho hmem
    have h1 : β o ∈ (y : PrimeSpectrum F).asIdeal := hmem
    have hp : (y : PrimeSpectrum F).asIdeal.IsPrime := PrimeSpectrum.isPrime (y : PrimeSpectrum F)
    have h2 : (y : PrimeSpectrum F).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [h2, Ideal.mem_bot] at h1
    exact ho (hβ (by rw [h1, map_zero]))
  · intro hx
    refine ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum F), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap β ⊥ = x.asIdeal
    ext o
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      rw [(injective_iff_map_eq_zero β).1 hβ o h]
      exact zero_mem _
    · intro hmem
      by_contra hne
      exact hx o (fun h0 => hne (by rw [h0, map_zero])) hmem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem lieMult_pt (Y : Model Xo c β) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) {Ω : Type} [Field Ω]
    (i : c.F →+* Ω) (y : Sp Ω ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap i) :
    LieMult Y.t.act (y ≫ Y.j) (i.comp (tauIn c τ)) D.p ∧
      LieMult Y.t.act (y ≫ Y.j) (i.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q := by
  haveI := Y.oF.t.semi.smooth
  let K := AlgebraicClosure Ω
  let e : Ω →+* K := algebraMap Ω K
  have hx : (spMap e ≫ y) ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s) =
      spMap (e.comp (i.comp (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [pullback.condition, ← Category.assoc, Category.assoc _ y, hy]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hdet := (Y.oF.geom K (spMap e ≫ y) _ hx).1
  have key : ∀ (σ : 𝓞 E →+* Ω) (n : ℕ), LieMult Y.oF.t.act (spMap e ≫ y) (e.comp σ) n →
      LieMult Y.t.act (y ≫ Y.j) σ n := by
    intro σ n h
    rw [GlobalTheory.DetExtend.lieMult_extend] at h
    exact (GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ Y.t.G Y.oF.t.G Y.j Y.m.cm.F Y.t.act Y.oF.t.act
      Y.m.cart Y.m.act Ω y σ n).1 h
  have hρ : ∀ σ : E →+* ℂ, (e.comp (i.comp (tauIn c σ))) H.rt =
      (e.comp (i.comp (IntermediateField.inclusion c.le).toRingHom)) (baseKA l).ρ ↔ σ (H.rt : E) = H.rt0 := by
    intro σ
    simp only [RingHom.comp_apply]
    rw [e.injective.eq_iff, i.injective.eq_iff, Subtype.ext_iff]
    rfl
  refine ⟨key _ _ ((hdet (e.comp (i.comp (tauIn c τ)))).1 ((hρ τ).2 hτ)),
    key _ _ ((hdet (e.comp (i.comp (tauIn c (ComplexEmbedding.conjugate τ))))).2 ?_)⟩
  intro h
  have h1 := (hρ _).1 h
  rw [ComplexEmbedding.conjugate_coe_eq, hτ,
    GlobalTheory.CompanionTheory.Ar.EigRank.rt0_conj_neg_ne_zero H.d_prime.pos H.sqrt_neg_disc_sq] at h1
  have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h1
  have h0 : H.rt0 = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  have h3 := H.sqrt_neg_disc_sq
  rw [h0] at h3
  have h4 : (H.d : ℂ) = 0 := by linear_combination h3
  exact H.d_prime.ne_zero (by exact_mod_cast h4)

end PositivityTheory.Xgn.IntegralModelFacts

private theorem normalCpt_of_isNormalScheme_isCptGen {X : Scheme} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ) :
    GlobalTheory.CompanionTheory.Ar.Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨hdom, hic⟩ := hX p.1
  have hinj : Function.Injective (GlobalTheory.CompanionTheory.Ar.genMap ξ p) := hg.inj p
  have hfrac : ∀ z : Ω, ∃ r t : X.presheaf.stalk p.1, GlobalTheory.CompanionTheory.Ar.genMap ξ p t ≠ 0 ∧
      z * GlobalTheory.CompanionTheory.Ar.genMap ξ p t = GlobalTheory.CompanionTheory.Ar.genMap ξ p r := by
    intro z
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
    have hgU : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ U := p.2.mem_open U.2 hpU
    letI : Algebra Γ(X, U) (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
      (X.presheaf.germ U _ hgU).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨_, hgU⟩
    have hφ : ∀ u, GlobalTheory.CompanionTheory.Ar.genMap ξ p (X.presheaf.germ U p.1 hpU u) =
        (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U _ hgU u) := by
      intro u
      show (X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 ≫
        Scheme.stalkClosedPointTo ξ).hom u = _
      rw [← TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2]
      rfl
    obtain ⟨s, hs⟩ : ∃ s : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ),
        (Scheme.stalkClosedPointTo ξ).hom s = z := hg.bij.2 z
    obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (S := X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))
      (hU.primeIdealOf ⟨_, hgU⟩).asIdeal.primeCompl s
    refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU t, ?_, ?_⟩
    · rw [hφ]
      have hu : IsUnit (X.presheaf.germ U _ hgU (t : Γ(X, U))) :=
        IsLocalization.map_units (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) t
      exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
    · rw [hφ, hφ, ← hs]
      exact (map_mul (Scheme.stalkClosedPointTo ξ).hom _ _).symm.trans
        (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)
  letI : Algebra (X.presheaf.stalk p.1) Ω := (GlobalTheory.CompanionTheory.Ar.genMap ξ p).toAlgebra
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ (fun h => nonZeroDivisors.ne_zero hy (hinj (by
        rw [map_zero]; exact h)))
    · intro z
      obtain ⟨r, t, ht, hz⟩ := hfrac z
      exact ⟨⟨r, ⟨t, mem_nonZeroDivisors_of_ne_zero (fun h => ht (by rw [h, map_zero]))⟩⟩, hz⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩
  obtain ⟨P, hPm, hP⟩ := ha
  let e : X.presheaf.stalk p.1 ≃+* GlobalTheory.CompanionTheory.Ar.regAt ξ p :=
    RingEquiv.ofBijective (GlobalTheory.CompanionTheory.Ar.genMap ξ p).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), (GlobalTheory.CompanionTheory.Ar.genMap ξ p).rangeRestrict_surjective⟩
  have hcomp : (algebraMap (X.presheaf.stalk p.1) Ω).comp e.symm.toRingHom =
      algebraMap (GlobalTheory.CompanionTheory.Ar.regAt ξ p) Ω := by
    ext u
    change GlobalTheory.CompanionTheory.Ar.genMap ξ p (e.symm u) = (u : Ω)
    conv_rhs => rw [← e.apply_symm_apply u]
    rfl
  have hint : IsIntegral (X.presheaf.stalk p.1) a := by
    refine ⟨P.map e.symm.toRingHom, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hP
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨y, hy⟩

private theorem mem_range_pullback_fst_iff_unitAt {X : Scheme} {Ω O F : Type} [Field Ω] [CommRing O] [Field F]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (β : O →+* F)
    (hβ : Function.Injective β) (k : F →+* Ω) (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ)
    (hs : ξ ≫ s = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (k.comp β)) (x : GlobalTheory.CompanionTheory.Ar.Cpt ξ) :
    x.1 ∈ Set.range (pullback.fst s (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β)) ↔
      ∀ o : O, o ≠ 0 → GlobalTheory.CompanionTheory.Ar.unitAt ξ x (k (β o)) := by
  rw [Scheme.Pullback.range_fst, Set.mem_preimage,
    PositivityTheory.Xgn.IntegralModelFacts.mem_range_spMap β hβ]
  obtain ⟨θ, hθs⟩ := Spec.map_surjective (X.fromSpecStalk x.1 ≫ s)
  have hgen : ∀ o, GlobalTheory.CompanionTheory.Ar.genMap ξ x (θ.hom o) = k (β o) := by
    have e1 := GlobalTheory.CompanionTheory.Ar.LieCarrier.genMap_fromSpecStalk x
    have h1 : Spec.map (θ ≫ CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.genMap ξ x)) =
        Spec.map (CommRingCat.ofHom (k.comp β)) :=
      (Spec.map_comp _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.genMap ξ x)) ≫ ·) hθs).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s) e1).trans hs)))
    have h2 := Spec.map_injective h1
    intro o
    exact congrArg (fun f => f.hom o) h2
  have hcp := congrArg (fun f : Spec (X.presheaf.stalk x.1) ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O =>
    f (IsLocalRing.closedPoint (X.presheaf.stalk x.1))) hθs
  have hpt : s x.1 = Spec.map θ (IsLocalRing.closedPoint (X.presheaf.stalk x.1)) :=
    (congrArg s (Scheme.fromSpecStalk_closedPoint (X := X) (x := x.1))).symm.trans hcp.symm
  have hmem : (s x.1).asIdeal = Ideal.comap θ.hom (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)) :=
    congrArg PrimeSpectrum.asIdeal hpt
  refine forall_congr' fun o => imp_congr_right fun _ => ?_
  refine Iff.trans ?_ (GlobalTheory.CompanionTheory.Ar.unitAt_iff_of_isCptGen ξ hg x _).symm
  rw [hmem, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro hu
    exact ⟨θ.hom o, hu, hgen o⟩
  · rintro ⟨u, hu, hu'⟩
    rw [← hgen o] at hu'
    rwa [← hg.inj x hu']

open PositivityTheory.Xgn.IntegralModelFacts in
theorem PositivityTheory.Xgn.integral_model_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ hβ hfrac hτ
  haveI := Y.t.semi.smooth
  have hlie := PositivityTheory.Xgn.IntegralModelFacts.lieMult_pt Y τ hτ Z.inc Z.ξ₀ Z.over_inc
  have hs : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j_s, ← Category.assoc, Z.over_inc]
    simp only [spMap, ← Spec.map_comp]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.projProper O Y.X Y.s Y.proj, normalCpt_of_isNormalScheme_isCptGen _ Y.normal Z.gen, hs,
    fun x => mem_range_pullback_fst_iff_unitAt _ Y.s β hβ Z.inc Z.gen hs x,
    (PositivityTheory.HtPt.Htat.lie_fin _ _ _ _ _ Z.M).1, ?_, ?_⟩
  · exact GlobalTheory.CompanionTheory.Ar.EigRank.finrank_eigSp_of_lieMult _ _ _ _ _ _ _ _ _ Z.M Z.ρ Z.act hlie.1
  · exact GlobalTheory.CompanionTheory.Ar.EigRank.finrank_eigSp_of_lieMult _ _ _ _ _ _ _ _ _ Z.M Z.ρ Z.act hlie.2
