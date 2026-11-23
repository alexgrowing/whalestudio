import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameOfGeoRead
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.TraceRuleSec

theorem isIntegral_of_forall_valuationSubring {L : Type} [Field L] (A : Subring L) (x : L)
    (h : ∀ V : ValuationSubring L, A ≤ V.toSubring → x ∈ V) : IsIntegral A x := by
  by_contra hx
  have hx0 : x ≠ 0 := fun e => hx (e ▸ isIntegral_zero)
  let B : Subalgebra A L := Algebra.adjoin A {x⁻¹}
  have hyB : x⁻¹ ∈ B := Algebra.subset_adjoin rfl
  let y : B.toSubring := ⟨x⁻¹, hyB⟩
  have hnu : ¬ IsUnit y := by
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hwx : (w : L) = x := by
      have : x⁻¹ * (w : L) = 1 := congrArg Subtype.val hw
      field_simp at this
      exact this
    have hxB : x ∈ Algebra.adjoin A ({x⁻¹} : Set L) := by
      have := w.2
      rw [hwx] at this
      exact this
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hxB
    obtain ⟨p, hp⟩ := hxB
    apply hx
    letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
    have e1 := Polynomial.eval₂_reverse_mul_pow (algebraMap A L) x⁻¹ p
    have e2 : ⅟(x⁻¹) = x := by simp
    rw [e2] at e1
    have e3 : Polynomial.eval₂ (algebraMap A L) x⁻¹ p = x := by
      have := hp
      simpa [Polynomial.aeval_def] using this
    rw [e3] at e1
    have hle : p.reverse.natDegree ≤ p.natDegree := Polynomial.reverse_natDegree_le p
    refine ⟨Polynomial.X ^ (p.natDegree + 1) - p.reverse, ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hle)
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, sub_eq_zero]
      have h5 : (x⁻¹) ^ p.natDegree * x ^ p.natDegree = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow]
      generalize Polynomial.eval₂ (algebraMap A L) x p.reverse = Q at e1
      calc x ^ (p.natDegree + 1) = x * x ^ p.natDegree := by rw [pow_succ, mul_comm]
        _ = Q * (x⁻¹ ^ p.natDegree * x ^ p.natDegree) := by
          nth_rewrite 1 [← e1]
          ring
        _ = Q := by rw [h5, mul_one]
  let I : Ideal B.toSubring := Ideal.span {y}
  have hI : I ≠ ⊤ := fun e => hnu (Ideal.span_singleton_eq_top.1 e)
  obtain ⟨V, hBV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hAV : A ≤ V.toSubring := fun a ha => hBV (by
    exact B.algebraMap_mem ⟨a, ha⟩)
  have hxV := h V hAV
  have hy : x⁻¹ ∈ V.nonunits := hIV ⟨y, Ideal.mem_span_singleton_self y, rfl⟩
  have := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 hy
  obtain ⟨hyV, hm⟩ := this
  exact (IsLocalRing.mem_maximalIdeal _).1 hm (IsUnit.of_mul_eq_one (⟨x, hxV⟩ : V) (Subtype.ext (by simp [hx0])))

theorem trace_mem {K L : Type} [Field K] [Field L] (R : Subring K) (φ : K →+* L)
    (hR : ∀ a : K, IsIntegral R a → a ∈ R) (x : L)
    (hx : ∀ V : ValuationSubring L, (∀ a : R, φ a ∈ V) → x ∈ V) :
    letI := φ.toAlgebra; Algebra.trace K L x ∈ R := by
  letI := φ.toAlgebra
  by_cases hf : FiniteDimensional K L
  · have h1 : IsIntegral (R.map φ) x := isIntegral_of_forall_valuationSubring _ x fun V hV =>
      hx V fun a => hV ⟨a, a.2, rfl⟩
    letI : Algebra R L := (φ.comp R.subtype).toAlgebra
    haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun a => rfl
    have h2 : IsIntegral R x := by
      obtain ⟨p, hp, hp0⟩ := h1
      let f : R →+* R.map φ := (φ.comp R.subtype).codRestrict (R.map φ) fun a => ⟨a, a.2, rfl⟩
      have hs : Function.Surjective f := fun b => by
        obtain ⟨a, ha, hab⟩ := b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
      obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
        ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective f hs p)) hp
      refine ⟨q, hqm, ?_⟩
      rw [← hq, Polynomial.eval₂_map] at hp0
      exact hp0
    exact hR _ (Algebra.isIntegral_trace h2)
  · rw [Algebra.trace_eq_zero_of_not_exists_basis]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hf (Module.Basis.finiteDimensional_of_finite b)

theorem exists_chart {K : Type} {ι : K → Type} [∀ k, Finite (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (V : ValuationSubring Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∃ cc : (k : K) → ι k, (∀ k, y ⟨k, cc k⟩ ≠ 0) ∧ ∀ k i, y ⟨k, i⟩ / y ⟨k, cc k⟩ ∈ V := by
  have key : ∀ k, ∃ c : ι k, y ⟨k, c⟩ ≠ 0 ∧ ∀ i, y ⟨k, i⟩ / y ⟨k, c⟩ ∈ V := fun k => by
    obtain ⟨i₀, hi₀⟩ := hy k
    haveI : Nonempty (ι k) := ⟨i₀⟩
    obtain ⟨c, hc⟩ := Finite.exists_max fun i => V.valuation (y ⟨k, i⟩)
    have hc0 : y ⟨k, c⟩ ≠ 0 := fun e => by
      have := hc i₀
      rw [e, map_zero] at this
      exact hi₀ ((V.valuation).zero_iff.1 (le_zero_iff.1 this))
    refine ⟨c, hc0, fun i => ?_⟩
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc i) zero_le'
  choose cc h1 h2 using key
  exact ⟨cc, h1, h2⟩

end GlobalTheory.CompanionTheory.Ar.Plug.TraceRuleSec

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.TraceRuleSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem prod_ix {M : Type} [CommMonoid M] (g : Ix Dw → M) (h0 : g none = 1) :
    ∏ i, g i = ∏ r : RootIx Dw, g (Small.rootFrameIx Dw r) := by
  let f : RootIx Dw ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    Equiv.ofBijective _ ((GlobalTheory.CompanionTheory.Ar.Rec.FinRd.labelSig_bijective Dw).comp (GlobalTheory.CompanionTheory.Ar.Rec.FinRd.rootIdx_bijective Dw))
  rw [← Fintype.prod_equiv (Equiv.optionCongr f) (fun o => g (Option.map f o)) g (fun _ => rfl), Fintype.prod_option]
  simp only [Option.map_none, Option.map_some]
  rw [h0, one_mul]
  rfl

theorem exOf_root (u : GlobalTheory.AllWt.Weight Dw) (r : RootIx Dw) :
    GlobalTheory.AllWt.exOf Dw u 0 (Small.rootFrameIx Dw r) = HodgeCpt.rootSgn Dw r * u r.1 r.2 := by
  obtain ⟨τ, n⟩ := r
  by_cases h : (n : ℕ) < Dw.p
  · have e1 : GlobalTheory.AllWt.exOf Dw u 0 (Small.rootFrameIx Dw (τ, n)) = (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ.1, n) :=
      congrArg (fun x : Σ s, Fin (labelRk Dw s) => (GlobalTheory.AllWt.wtOf Dw u 0).1 (Small.labelC x.1, (x.2 : ℕ)))
        (GlobalTheory.CompanionTheory.Ar.Rec.FinRd.rootIdx_lt Dw (τ := τ) h)
    rw [e1, GlobalTheory.AllWt.wtOf_big _ _ τ _ h]
    simp [HodgeCpt.rootSgn, h]
  · have e1 : GlobalTheory.AllWt.exOf Dw u 0 (Small.rootFrameIx Dw (τ, n)) =
        (GlobalTheory.AllWt.wtOf Dw u 0).1 (conjEmb τ.1, Dw.p + Dw.q - 1 - n) :=
      congrArg (fun x : Σ s, Fin (labelRk Dw s) => (GlobalTheory.AllWt.wtOf Dw u 0).1 (Small.labelC x.1, (x.2 : ℕ)))
        (GlobalTheory.CompanionTheory.Ar.Rec.FinRd.rootIdx_ge Dw (τ := τ) h)
    have hn := n.2
    rw [e1, GlobalTheory.AllWt.wtOf_small _ _ τ _ (by omega)]
    have : (⟨Dw.p + (Dw.q - 1 - (Dw.p + Dw.q - 1 - (n : ℕ))), by omega⟩ : Fin (Dw.p + Dw.q)) = n := Fin.ext (by
      show Dw.p + (Dw.q - 1 - (Dw.p + Dw.q - 1 - (n : ℕ))) = n
      omega)
    simp [HodgeCpt.rootSgn, h, this]

theorem zpow_sum_exp {G I : Type} [CommGroup G] (g : G) (s : Finset I) (f : I → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem unit_calc {G K : Type} [CommGroup G] [Fintype K] (tt ph : Ix Dw → G) (u : GlobalTheory.AllWt.Weight Dw)
    (v ee : RootIx Dw → G) (yy : K → G) (xd : RootIx Dw → K → ℤ) (a : K → ℤ)
    (hw : GlobalTheory.AllWt.exOf Dw u 0 none = 0)
    (hd : ∀ r, ((tt⁻¹ * ph) (Small.rootFrameIx Dw r)) ^ HodgeCpt.rootSgn Dw r = v r * ((∏ k, yy k ^ xd r k) * ee r))
    (ha : ∀ k, a k = ∑ r, - u r.1 r.2 * xd r k) :
    (∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * ((∏ i, tt i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * ∏ r, ee r ^ u r.1 r.2)⁻¹ =
      (∏ r, v r ^ u r.1 r.2) * ∏ k, yy k ^ (-a k) := by
  have h1 : (∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * (∏ i, tt i ^ GlobalTheory.AllWt.exOf Dw u 0 i)⁻¹ =
      ∏ i, ((tt⁻¹ * ph) i) ^ GlobalTheory.AllWt.exOf Dw u 0 i := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow]
    rw [mul_comm]
  have h2 : ∏ i, ((tt⁻¹ * ph) i) ^ GlobalTheory.AllWt.exOf Dw u 0 i =
      ∏ r : RootIx Dw, (v r * ((∏ k, yy k ^ xd r k) * ee r)) ^ u r.1 r.2 := by
    rw [prod_ix _ (by rw [hw, zpow_zero])]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [exOf_root, zpow_mul, hd r]
  have h3 : ∏ r : RootIx Dw, (∏ k, yy k ^ xd r k) ^ u r.1 r.2 = ∏ k, yy k ^ (-a k) := by
    simp only [ha, ← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib, zpow_sum_exp]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [← zpow_mul]
    congr 1
    ring
  rw [mul_inv, ← mul_assoc, h1, h2]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [h3]
  group

end GlobalTheory.CompanionTheory.Ar.Plug.TraceRuleSec

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.TraceRuleSec

theorem chart_reg : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (C : GlobalTheory.Reg.FChart h) (Rd : Reading Fr h C.Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1, ((∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (Om C.Z)ˣ) : Om C.Z) * trOf Rd u s ∈ C.R := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y _ T o B b Fr C Rd hg u s hs
  letI := Small.cstAlg (o.toTowerOrigin.Or B b)
  obtain ⟨φ, P, t, hφ, hP, hbor, ht⟩ := GlobalTheory.CompanionTheory.Ar.Plug.RdGeo.frame_of_geoRead hG E H Dw l Xo c r U h e hC Y T o B b Fr C.Z Rd hg
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hGr := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (T.M B b).Ω
  obtain ⟨z, hz⟩ := hL.bc _ _ φ C.yg
  have hψ : FrMap (φ.comp C.R.val) C.y z := frMap_trans _ _ _ C.R.val φ C.y C.yg z C.gen hz
  have hb := frBorBC _ _ φ C.t (genFr h C.Z) C.yg P z C.bor hP hz
  have hd := hGr.2.1 _ _ _ _ _ (hGr.2.2.1 _ _ _ hbor) hb
  set a0 : Om C.Z := ((∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (Om C.Z)ˣ) : Om C.Z) with ha0
  have htr : a0 * trOf Rd u s = (letI := Rd.φ.toAlgebra; Algebra.trace (Om C.Z) (T.M B b).Ω (Rd.φ a0 * (s / gauge Rd u))) := by
    letI := Rd.φ.toAlgebra
    have : Rd.φ a0 * (s / gauge Rd u) = a0 • (s / gauge Rd u) := by
      rw [Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul]
    rfl
  have hR : ∀ a : Om C.Z, IsIntegral C.R.toSubring a → a ∈ C.R.toSubring := fun a ha => by
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI : IsFractionRing C.R (Om C.Z) := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨p, hp, q, hq, hq0, e'⟩ := C.frac x
      exact ⟨⟨p, hp⟩, ⟨q, hq⟩, by
        show x = p / q
        rw [eq_div_iff hq0, e']⟩
    have ha' : IsIntegral C.R a := ha
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 ha'
    exact y.2
  have hx : ∀ V : ValuationSubring (T.M B b).Ω, (∀ a : C.R.toSubring, Rd.φ a ∈ V) →
      Rd.φ a0 * (s / gauge Rd u) ∈ V := by
    intro V hV
    have hy : ∀ k, ∃ i, (T.M B b).y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨c', hc'⟩ := (o.toTowerOrigin.Or B b).𝔐.tie.cover ⟨GlobalTheory.CompanionTheory.Ar.genPt (o.toTowerOrigin.Or B b).𝔐.ξ, specializes_rfl⟩
      exact ⟨c' k, (Finset.prod_ne_zero_iff.1 hc'.1) k (Finset.mem_univ k)⟩
    obtain ⟨cc, h1, h2⟩ := exists_chart (T.M B b).y V hy
    have hVψ : ∀ x, (φ.comp C.R.val) x ∈ V := fun x => by
      have := hV x
      rw [← hφ] at this
      exact this
    choose v hv using GlobalTheory.T.root_origin_generic_frame_relay E H Dw l Xo c Y (o.S B) (T.M B b) (o.Sys b) (o.Fx b) (o.toTowerOrigin.Or B b) Fr h C V (φ.comp C.R.val) z _ hψ hd hVψ cc h1 h2
    let yy : (T.M B b).K → ((T.M B b).Ω)ˣ := fun k => Units.mk0 _ (h1 k)
    let ee : RootIx Dw → ((T.M B b).Ω)ˣ := fun r => Units.mk0 _ ((o.toTowerOrigin.Or B b).lines r).1
    let ph : Ix Dw → ((T.M B b).Ω)ˣ := fun i => Units.map (φ : Om C.Z →* (T.M B b).Ω) (C.t i)
    let vv : RootIx Dw → ((T.M B b).Ω)ˣ := fun r => Units.map (V.subtype : V →* (T.M B b).Ω) (v r)
    have hw0 : GlobalTheory.AllWt.exOf Dw u 0 none = 0 := by
      show (2 : ℤ) * 0 = 0
      simp
    have hdeg : ∀ k, degOf (T.M B b) u k = ∑ r : RootIx Dw, - u r.1 r.2 * (T.M B b).xdeg r k := fun k => by
      show (∑ j, nOf u j • ((T.M B b).line 1 j).a) k = _
      rw [Fintype.sum_option]
      simp only [nOf, zero_smul, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      show _ * ((T.M B b).x 1 r).a k = _
      rw [(T.M B b).x_deg]
    have hcalc := unit_calc t ph u vv ee yy (T.M B b).xdeg (degOf (T.M B b) u) hw0 (fun r => Units.ext (by
      have := hv r
      simpa [yy, ee, vv, ph] using this)) hdeg
    have hs' := hs cc h1
    have e1 : Rd.φ a0 = ((∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i : ((T.M B b).Ω)ˣ) : (T.M B b).Ω) := by
      rw [← hφ, ha0]
      have : (∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i) =
          Units.map (φ : Om C.Z →* (T.M B b).Ω) (∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i) := by
        simp only [map_prod, map_zpow, ph]
      rw [this]
      rfl
    have e2 : gauge Rd u = (((∏ i, t i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * ∏ r : RootIx Dw, ee r ^ u r.1 r.2 : ((T.M B b).Ω)ˣ) : (T.M B b).Ω) := by
      have e3 : (∏ i, Rd.t i ^ Rec.exZ Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 i : ((T.M B b).Ω)ˣ) = ∏ i, t i ^ GlobalTheory.AllWt.exOf Dw u 0 i := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rcases i with _ | x
        · rw [hw0]
          show _ ^ (0 : ℤ) = _
          simp
        · rw [ht _ (by simp)]
          rfl
      have e3b : (∏ r : RootIx Dw, (o.toTowerOrigin.Or B b).e r ^ (-nOf u (some r))) =
          ((∏ r : RootIx Dw, ee r ^ u r.1 r.2 : ((T.M B b).Ω)ˣ) : (T.M B b).Ω) := by
        rw [Units.coe_prod]
        refine Finset.prod_congr rfl fun r _ => ?_
        simp [nOf, ee]
      rw [gauge, e3, e3b, Units.val_mul]
    have e4 : Rd.φ a0 * (s / gauge Rd u) =
        ((∏ r : RootIx Dw, vv r ^ u r.1 r.2 : ((T.M B b).Ω)ˣ) : (T.M B b).Ω) *
          (s * ∏ k, (T.M B b).y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf (T.M B b) u k))) := by
      have e5 := congrArg (Units.val) hcalc
      rw [Units.val_mul, Units.val_mul] at e5
      have e6 : ((∏ k, yy k ^ (-degOf (T.M B b) u k) : ((T.M B b).Ω)ˣ) : (T.M B b).Ω) =
          ∏ k, (T.M B b).y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf (T.M B b) u k)) := by
        rw [Units.coe_prod]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp [yy]
      rw [e6] at e5
      rw [e1, e2, div_eq_mul_inv, ← Units.val_inv_eq_inv_val]
      calc _ = (((∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i : ((T.M B b).Ω)ˣ) : (T.M B b).Ω) * (((∏ i, t i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * ∏ r : RootIx Dw, ee r ^ u r.1 r.2 : ((T.M B b).Ω)ˣ)⁻¹ : ((T.M B b).Ω)ˣ)) * s := by ring
        _ = _ := by rw [e5]; ring
    rw [e4]
    have hinc : ∀ x ∈ chartRingZ (T.M B b).y cc, x ∈ V := fun x hx => by
      have hle : chartRingZ (T.M B b).y cc ≤ subalgebraOfSubring V.toSubring :=
        Algebra.adjoin_le (by
          rintro _ ⟨p, rfl⟩
          exact h2 p.1 p.2)
      exact hle hx
    have hσ : s * ∏ k, (T.M B b).y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf (T.M B b) u k)) ∈ V := by
      have hi : IsIntegral V (s * ∏ k, (T.M B b).y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf (T.M B b) u k))) := by
        obtain ⟨p, hp, hp0⟩ := hs'
        let f : chartRingZ (T.M B b).y cc →+* V :=
          { toFun := fun x => ⟨x, hinc x x.2⟩, map_one' := rfl, map_zero' := rfl, map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
        refine ⟨p.map f, hp.map f, ?_⟩
        rw [Polynomial.eval₂_map]
        exact hp0
      obtain ⟨y', hy'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
      rw [← hy']
      exact y'.2
    refine mul_mem ?_ hσ
    have : (∏ r : RootIx Dw, vv r ^ u r.1 r.2) = Units.map (V.subtype : V →* (T.M B b).Ω) (∏ r : RootIx Dw, v r ^ u r.1 r.2) := by
      simp only [map_prod, map_zpow, vv]
    rw [this]
    exact ((∏ r : RootIx Dw, v r ^ u r.1 r.2 : Vˣ) : V).2
  rw [htr]
  exact trace_mem C.R.toSubring Rd.φ hR _ hx

end GlobalTheory.CompanionTheory.Ar.Plug.TraceRuleSec

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem exists_section_of_trace : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1, ∃ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z ∧ evC h Z f = trOf Rd u s := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y _ T o B b Fr Z Rd hgeo u s hs
  classical
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  let bb : ∀ Z' : Comp Xo c, Om Z' := fun Z' => if hZ : Z' = Z then hZ ▸ trOf Rd u s else 0
  have hbb : bb Z = trOf Rd u s := dif_pos rfl
  obtain ⟨g, hg, hgv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (GlobalTheory.AllWt.exOf Dw u 0) bb (fun C => by
    by_cases hZ : C.Z = Z
    · subst hZ
      rw [hbb]
      exact TraceRuleSec.chart_reg hG E H Dw l Xo c r U h e hC Y T o B b Fr C Rd hgeo u s hs
    · have : bb C.Z = 0 := dif_neg hZ
      rw [this, mul_zero]
      exact zero_mem _)
  have hm := GlobalTheory.FlatLine.idem_mul_mem Z hg
  refine ⟨GlobalTheory.FlatLine.idem Z * g, hm.1, hm.2, ?_⟩
  have h3 : evC h Z (GlobalTheory.FlatLine.idem Z) = 1 := GlobalTheory.FlatLine.evR_idem (GlobalTheory.AllWt.liesOn_genFr h Z) (hL.test _ _)
  show evR Xo c (GlobalTheory.FlatLine.idem Z * g) (genFr h Z) = _
  have h4 : evR Xo c (GlobalTheory.FlatLine.idem Z * g) (genFr h Z) = evC h Z (GlobalTheory.FlatLine.idem Z) * evC h Z g :=
    Formalism.L2.Pj.evalAt_mul _ _ _ _ _
  rw [h4, h3, one_mul, hgv Z, hbb]

theorem _root_.GlobalTheory.CompanionTheory.Relay.comp_laws_tower_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1, ∃ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z ∧ evC h Z f = trOf Rd u s :=
  GlobalTheory.CompanionTheory.Ar.Plug.exists_section_of_trace

end GlobalTheory.CompanionTheory.Ar.Plug
