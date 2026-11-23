import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCompleteDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingOfMinimal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapClosedPointOfSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.BdDim GlobalTheory.Models GlobalTheory.LN GlobalTheory.Toroidal GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmallTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_unif_ext_card (T : CDVR) (hT : Cardinal.mk T.V ≤ Cardinal.continuum) (t : SAB H (Sp T.V))
    (hp : PolAt t (jK T.V)) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ IsLocalHom φ ∧
      Cardinal.mk T'.V ≤ Cardinal.continuum ∧
      Nonempty (SABMap t' t (spMap φ)) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t.G t.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  exact ⟨{ V := W }, algebraMap T.V W, _, hi, hl,
    GlobalTheory.ArcIntegral.mk_le_continuum_of_finite (algebraMap T.V W) (RingHom.finite_algebraMap.2 hf) hT, ⟨m⟩, ⟨P⟩⟩

theorem spMap_field_point {A V K : Type} [CommRing A] [CommRing V] [Field K] (φ : A →+* V) (i : V →+* K)
    (hi : Function.Injective i) (p : Sp K) : ((spMap i ≫ spMap φ) p).asIdeal = RingHom.ker φ := by
  rw [GlobalTheory.ArcIntegral.sp_comp]
  change Ideal.comap (i.comp φ) p.asIdeal = _
  rw [@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime, ← Ideal.comap_comap, Ideal.comap_bot_of_injective _ hi]
  rfl

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem exists_small_base_trait (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Y.X) (hx : x ∉ abLocus Y.t.G) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Y.X) (y : Sp (FractionRing T.V) ⟶ Xo.XF c), Cardinal.mk T.V ≤ Cardinal.continuum ∧
      χ (closedPoint T.V : Sp T.V) = x ∧ y ≫ Y.j = jK T.V ≫ χ := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨hβ, -, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  obtain ⟨-, -, -, _, _, -, -⟩ := GlobalTheory.ModelRelCompare.densePart Y hβ
  obtain ⟨T, χ, y, rfl, hy⟩ := exists_base_trait Y hβ x
  haveI : Countable (𝓞 c.F) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  let x : Y.X := χ (closedPoint T.V : Sp T.V)
  let A : Type := Y.X.presheaf.stalk x
  have hA : Countable A := GlobalTheory.SpecialStalk.countable_stalk Y.s x
  let φ : A →+* T.V := (Scheme.stalkClosedPointTo (R := .of T.V) χ).hom
  have hφl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo (R := .of T.V) χ).hom)
  let f : Sp A ⟶ Y.X := Y.X.fromSpecStalk x
  have hfac : spMap φ ≫ f = χ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T.V) χ
  have hfc : f (closedPoint A : Sp A) = x := Scheme.fromSpecStalk_closedPoint
  let q : Sp (FractionRing T.V) := (⊥ : PrimeSpectrum (FractionRing T.V))
  have hq := spMap_field_point φ (algebraMap T.V (FractionRing T.V)) (IsFractionRing.injective _ _) q
  have hgen : f ((spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap φ) q) ∈ Set.range Y.j := by
    refine ⟨y q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hy, Category.assoc, hfac]
  have hne : ∃ a ∈ maximalIdeal A, φ a ≠ 0 := by
    by_contra hn
    push Not at hn
    have e : (spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap φ) q = (closedPoint A : Sp A) := by
      apply PrimeSpectrum.ext
      refine ((maximalIdeal.isMaximal A).eq_of_le
        ((spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap φ) q).isPrime.ne_top ?_).symm
      rw [hq]
      exact hn
    rw [e, hfc] at hgen
    exact hx (GlobalTheory.ArcIntegral.range_j_subset Y hgen)
  obtain ⟨T', ψ, hψ, hker, hcard⟩ := GlobalTheory.T.exists_countable_complete_dvr_extension A T.V φ hA hφl hne
  obtain ⟨y', hy'⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset Y.j
    (spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap ψ ≫ f) (by
      rintro _ ⟨p, rfl⟩
      have e : (spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap ψ) p =
          (spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap φ) q :=
        PrimeSpectrum.ext (((spMap_field_point ψ _ (IsFractionRing.injective _ _) p).trans hker).trans hq.symm)
      rw [← Category.assoc, Scheme.Hom.comp_apply, e]
      exact hgen)
  refine ⟨T', spMap ψ ≫ f, y', hcard, ?_, hy'⟩
  exact (Scheme.Hom.comp_apply (spMap ψ) f _).trans ((congrArg f (comap_closedPoint ψ)).trans hfc)

theorem exists_detCond {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X}
    {t : SAB H S} (m : SABMap t Y.t χ) (s : Sp ℂ ⟶ S) (z : Sp ℂ ⟶ Xo.XF c) (hz : z ≫ Y.j = s ≫ χ) :
    ∃ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) ∧ DetCond D t.act s ρ := by
  let β' : KA l →+* ℂ := (Spec.preimage (z ≫ pullback.fst Xo.s
    (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)).hom
  have hx : z ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β' := by
    refine Eq.symm ?_
    show Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hdet := (Y.oF.geom ℂ z β' hx).1
  have key : ∀ τ n, LieMult Y.oF.t.act z τ n → LieMult t.act s τ n := by
    intro τ n hn
    have h₅ := (lieMult_iff_of_isGrpPullback Y.m.cart Y.oF.t.act Y.t.act Y.m.act z τ n).1 hn
    have hz' : z ≫ Y.jQ ≫ pullback.fst _ _ = s ≫ χ := hz
    rw [hz'] at h₅
    exact (lieMult_iff_of_isGrpPullback m.cart t.act Y.t.act m.act _ τ n).2 h₅
  refine ⟨β' (baseKA l).ρ, ?_, fun τ => ⟨fun h => key _ _ ((hdet τ).1 h), fun h => key _ _ ((hdet τ).2 h)⟩⟩
  rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]

theorem exists_unif_trait_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Y.X), 1 ≤ D.p + D.q → x ∉ abLocus Y.t.G → ∃ (T : Formalism.L2.Pj.CDVR) (σ : T.V →+* ℂ) (y : Sp T.V ⟶ Y.X) (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (ρ : ℂ), Function.Injective σ ∧ y (closedPoint T.V : Sp T.V) = x ∧ Nontrivial P.D.toPre.X ∧ ρ ^ 2 = -(H.d : ℂ) ∧ ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult t.act (spMap σ) τ D.p) ∧ (τ H.rt ≠ ρ → LieMult t.act (spMap σ) τ D.q) := by
  intro E _ _ _ H D l Xo c Y x _ hx
  obtain ⟨T, χ, y, hT, hc, hy⟩ := exists_small_base_trait Y x hx
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull χ Y.t
  have hp := GlobalTheory.GoodTrait.polAt_of_point Y m (jK T.V) y hy
  obtain ⟨T', φ, t', hi, hl, hT', ⟨m'⟩, ⟨P⟩⟩ := exists_unif_ext_card T hT _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  haveI : CharZero (FractionRing T'.V) := charZero_of_injective_ringHom (IsFractionRing.injective T'.V _)
  obtain ⟨κ⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex_of_le_continuum (FractionRing T'.V)
    (by rwa [Cardinal.mk_fractionRing])
  let σ : T'.V →+* ℂ := κ.comp (algebraMap T'.V (FractionRing T'.V))
  have hσ : Function.Injective σ := κ.injective.comp (IsFractionRing.injective _ _)
  obtain ⟨g, hg⟩ := GlobalTheory.ArcIntegral.exists_frac_lift (K := FractionRing T.V) (σ.comp φ) (hσ.comp hi)
  have hcl : (spMap φ ≫ χ) (closedPoint T'.V : Sp T'.V) = x :=
    (Scheme.Hom.comp_apply (spMap φ) χ _).trans ((congrArg χ (comap_closedPoint φ)).trans hc)
  obtain ⟨ρ, hρ, hdet⟩ := exists_detCond Y n (spMap σ) (spMap g ≫ y) (by
    rw [Category.assoc, hy, ← Category.assoc, ← Category.assoc, GlobalTheory.ArcIntegral.sp_comp σ φ, ← hg,
      ← GlobalTheory.ArcIntegral.sp_comp])
  refine ⟨T', σ, spMap φ ≫ χ, t', n, P, ρ, hσ, hcl, ?_, hρ, hdet⟩
  refine not_subsingleton_iff_nontrivial.1 fun hs => hx ?_
  rw [← hcl]
  exact (abLocus_pullback abLocusOne Y.t.semi n.cart.1 _).2 ((closed_mem_abLocus_iff T' P).2 hs)

end GlobalTheory.SmallTrait

end
