import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameRelayStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsEquivOfGivenStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentity
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsRootModelRelayStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.BirEx

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

def gaugeT {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
    {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
    (Or : RootOrigin Y S RM Fx) (t : Ix Dw → (RM.Ω)ˣ) (u : GlobalTheory.AllWt.Weight Dw) : RM.Ω :=
  ((∏ i, t i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (RM.Ω)ˣ) : RM.Ω) * ∏ r : RootIx Dw, Or.e r ^ u r.1 r.2

theorem mem_val_of_chart (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) : letI := Small.cstAlg Or
    ∀ (φ : Om C.Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h C.Z) P → FrBor t P Fr.y₀ →
    ∀ (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm RM.y (degOf RM u) 1, ∀ V : ValuationSubring RM.Ω, (∀ a : C.R, φ a ∈ V) →
      φ ((∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (Om C.Z)ˣ) : Om C.Z) * (s / gaugeT Or t u) ∈ V := by
  letI := Small.cstAlg Or
  intro φ P t hP hbor u s hs V hV
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hGr := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c RM.Ω
  obtain ⟨z, hz⟩ := hL.bc _ _ φ C.yg
  have hψ : FrMap (φ.comp C.R.val) C.y z := frMap_trans _ _ _ C.R.val φ C.y C.yg z C.gen hz
  have hb := frBorBC _ _ φ C.t (genFr h C.Z) C.yg P z C.bor hP hz
  have hd := hGr.2.1 _ _ _ _ _ (hGr.2.2.1 _ _ _ hbor) hb
  have hy : ∀ k, ∃ i, RM.y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨c', hc'⟩ := Or.𝔐.tie.cover ⟨GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ, specializes_rfl⟩
    exact ⟨c' k, (Finset.prod_ne_zero_iff.1 hc'.1) k (Finset.mem_univ k)⟩
  obtain ⟨cc, h1, h2⟩ := exists_chart RM.y V hy
  have hVψ : ∀ x, (φ.comp C.R.val) x ∈ V := fun x => hV x
  choose v hv using GlobalTheory.T.root_origin_generic_frame_relay E H Dw l Xo c Y S RM Sys Fx Or Fr h C V (φ.comp C.R.val) z _ hψ hd hVψ cc h1 h2
  let yy : RM.K → (RM.Ω)ˣ := fun k => Units.mk0 _ (h1 k)
  let ee : RootIx Dw → (RM.Ω)ˣ := fun r => Units.mk0 _ (Or.lines r).1
  let ph : Ix Dw → (RM.Ω)ˣ := fun i => Units.map (φ : Om C.Z →* RM.Ω) (C.t i)
  let vv : RootIx Dw → (RM.Ω)ˣ := fun r => Units.map (V.subtype : V →* RM.Ω) (v r)
  have hw0 : GlobalTheory.AllWt.exOf Dw u 0 none = 0 := by
    show (2 : ℤ) * 0 = 0
    simp
  have hdeg : ∀ k, degOf RM u k = ∑ r : RootIx Dw, - u r.1 r.2 * RM.xdeg r k := fun k => by
    show (∑ j, nOf u j • (RM.line 1 j).a) k = _
    rw [Fintype.sum_option]
    simp only [nOf, zero_smul, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    show _ * (RM.x 1 r).a k = _
    rw [RM.x_deg]
  have hcalc := unit_calc t ph u vv ee yy RM.xdeg (degOf RM u) hw0 (fun r => Units.ext (by
    have := hv r
    simpa [yy, ee, vv, ph] using this)) hdeg
  have hs' := hs cc h1
  set a0 : Om C.Z := ((∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (Om C.Z)ˣ) : Om C.Z) with ha0
  have e1 : φ a0 = ((∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (RM.Ω)ˣ) : RM.Ω) := by
    rw [ha0]
    have : (∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i) =
        Units.map (φ : Om C.Z →* RM.Ω) (∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i) := by
      simp only [map_prod, map_zpow, ph]
    rw [this]
    rfl
  have e2 : gaugeT Or t u = (((∏ i, t i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * ∏ r : RootIx Dw, ee r ^ u r.1 r.2 : (RM.Ω)ˣ) : RM.Ω) := by
    have e3b : (∏ r : RootIx Dw, Or.e r ^ u r.1 r.2) =
        ((∏ r : RootIx Dw, ee r ^ u r.1 r.2 : (RM.Ω)ˣ) : RM.Ω) := by
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun r _ => ?_
      simp [ee]
    rw [gaugeT, e3b, Units.val_mul]
  have e4 : φ a0 * (s / gaugeT Or t u) =
      ((∏ r : RootIx Dw, vv r ^ u r.1 r.2 : (RM.Ω)ˣ) : RM.Ω) *
        (s * ∏ k, RM.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k))) := by
    have e5 := congrArg (Units.val) hcalc
    rw [Units.val_mul, Units.val_mul] at e5
    have e6 : ((∏ k, yy k ^ (-degOf RM u k) : (RM.Ω)ˣ) : RM.Ω) =
        ∏ k, RM.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k)) := by
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [yy]
    rw [e6] at e5
    rw [e1, e2, div_eq_mul_inv, ← Units.val_inv_eq_inv_val]
    calc _ = (((∏ i, ph i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (RM.Ω)ˣ) : RM.Ω) * (((∏ i, t i ^ GlobalTheory.AllWt.exOf Dw u 0 i) * ∏ r : RootIx Dw, ee r ^ u r.1 r.2 : (RM.Ω)ˣ)⁻¹ : (RM.Ω)ˣ)) * s := by ring
      _ = _ := by rw [e5]; ring
  rw [e4]
  have hinc : ∀ x ∈ chartRingZ RM.y cc, x ∈ V := fun x hx => by
    have hle : chartRingZ RM.y cc ≤ subalgebraOfSubring V.toSubring :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        exact h2 p.1 p.2)
    exact hle hx
  have hσ : s * ∏ k, RM.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k)) ∈ V := by
    have hi : IsIntegral V (s * ∏ k, RM.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k))) := by
      obtain ⟨p, hp, hp0⟩ := hs'
      let f : chartRingZ RM.y cc →+* V :=
        { toFun := fun x => ⟨x, hinc x x.2⟩, map_one' := rfl, map_zero' := rfl, map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
      refine ⟨p.map f, hp.map f, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp0
    obtain ⟨y', hy'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    rw [← hy']
    exact y'.2
  refine mul_mem ?_ hσ
  have : (∏ r : RootIx Dw, vv r ^ u r.1 r.2) = Units.map (V.subtype : V →* RM.Ω) (∏ r : RootIx Dw, v r ^ u r.1 r.2) := by
    simp only [map_prod, map_zpow, vv]
  rw [this]
  exact ((∏ r : RootIx Dw, v r ^ u r.1 r.2 : Vˣ) : V).2

end GlobalTheory.CompanionTheory.Ar.Plug.BirEx

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.BirEx

theorem surjective_of_finrank_one {K L : Type} [Field K] [Field L] (f : K →+* L)
    (h : letI := f.toAlgebra; Module.finrank K L = 1) : Function.Surjective f := by
  letI := f.toAlgebra
  intro w
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : L) one_ne_zero).1 h w
  exact ⟨a, by rw [← ha, Algebra.smul_def, mul_one]; rfl⟩

theorem adjoin_eq_top_of_ratios {F A B W : Type} [Field F] [Field A] [Field B] [Field W] [Algebra F A] (φ : A →+* B)
    (g : W →+* B) (hg : Function.Surjective g) {m : ℕ} (y : Fin (m + 1) → W)
    (hgen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) => y ij.1 / y ij.2) = ⊤)
    (i₀ : Fin (m + 1)) (hy : y i₀ ≠ 0) (v : Fin (m + 1) → A) (hv : ∀ i, φ (v i) = g (y i / y i₀)) :
    IntermediateField.adjoin F (Set.range v) = ⊤ := by
  set Aa := IntermediateField.adjoin F (Set.range v) with hAa
  have hle : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) => y ij.1 / y ij.2) ≤
      (Aa.toSubfield.map φ).comap g := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine ⟨v i / v j, ?_, ?_⟩
    · have hvm : ∀ i, v i ∈ Aa := fun i => IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
      exact div_mem (hvm i) (hvm j)
    · show φ (v i / v j) = g (y i / y j)
      rw [map_div₀, hv, hv, ← map_div₀, div_div_div_cancel_right₀ hy]
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨w, hw⟩ := hg (φ x)
  have h1 : w ∈ (Aa.toSubfield.map φ).comap g := hle (by rw [hgen]; trivial)
  obtain ⟨a, ha, e⟩ := h1
  have : a = x := φ.injective (e.trans hw)
  exact this ▸ ha

theorem mul_mem_chartLatNm {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (a a' : K → ℤ)
    (k₀ : K) (i i₀ : ι k₀) (q : ℕ) (hq : 0 < q) (ha : ∀ k, a' k = a k + if k = k₀ then (q : ℤ) else 0) {s : Ω}
    (hs : s ∈ chartLatNm y a 1) : s * (y ⟨k₀, i⟩ * y ⟨k₀, i₀⟩ ^ (q - 1)) ∈ chartLatNm y a' 1 := by
  intro c hc
  have h1 := hs c hc
  have hr : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ integralClosure (chartRingZ y c) Ω := fun p =>
    (integralClosure (chartRingZ y c) Ω).algebraMap_mem (⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩ : chartRingZ y c)
  have e : s * (y ⟨k₀, i⟩ * y ⟨k₀, i₀⟩ ^ (q - 1)) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) *
        ((y ⟨k₀, i⟩ / y ⟨k₀, c k₀⟩) * (y ⟨k₀, i₀⟩ / y ⟨k₀, c k₀⟩) ^ (q - 1)) := by
    have e1 : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
        (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * (y ⟨k₀, c k₀⟩ ^ q)⁻¹ := by
      have : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * (if k = k₀ then (y ⟨k, c k⟩ ^ q)⁻¹ else 1) := by
        intro k
        rw [ha k]
        split_ifs with hk
        · rw [show -(((1 : ℕ) : ℤ) * (a k + (q : ℤ))) = -(((1 : ℕ) : ℤ) * a k) + -(q : ℤ) by push_cast; ring,
            zpow_add₀ (hc k), zpow_neg _ (q : ℤ), zpow_natCast]
        · simp
      rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k₀]
      simp
    have hc0 := hc k₀
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [e1, Nat.add_sub_cancel, div_pow, pow_succ]
    field_simp
  rw [e]
  refine mul_mem h1 (mul_mem (hr ⟨k₀, i⟩) ?_)
  exact pow_mem (hr ⟨k₀, i₀⟩) _

theorem exists_rule_of_frame (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c) : letI := Small.cstAlg Or
    ∀ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P → FrBor t P Fr.y₀ →
    Function.Surjective φ → ∀ (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm RM.y (degOf RM u) 1,
      ∃ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), φ (evC h Z f) = s / gaugeT Or t u := by
  letI := Small.cstAlg Or
  intro φ P t hP hb hsurj u s hs
  classical
  obtain ⟨x, hx⟩ := hsurj (s / gaugeT Or t u)
  let bb : ∀ Z' : Comp Xo c, Om Z' := fun Z' => if hZ : Z' = Z then hZ ▸ x else 0
  have hbb : bb Z = x := dif_pos rfl
  obtain ⟨g, hg, hgv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (GlobalTheory.AllWt.exOf Dw u 0) bb (fun C => by
    by_cases hZ : C.Z = Z
    · subst hZ
      rw [hbb]
      set a0 : Om C.Z := ((∏ i, C.t i ^ GlobalTheory.AllWt.exOf Dw u 0 i : (Om C.Z)ˣ) : Om C.Z) with ha0
      let eq : Om C.Z ≃+* RM.Ω := RingEquiv.ofBijective (φ : Om C.Z →+* RM.Ω) ⟨φ.toRingHom.injective, hsurj⟩
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
      refine hR _ (isIntegral_of_forall_valuationSubring _ _ fun W hW => ?_)
      have h1 := mem_val_of_chart E H Dw l Xo c Y S RM Sys Fx Or Fr h C φ P t hP hb u s hs
        (W.comap (eq.symm : RM.Ω →+* Om C.Z)) (fun a => by
          rw [ValuationSubring.mem_comap]
          have : (eq.symm : RM.Ω →+* Om C.Z) (φ a) = a := eq.symm_apply_apply _
          rw [this]
          exact hW a.2)
      rw [ValuationSubring.mem_comap, ← hx, ← map_mul] at h1
      have : (eq.symm : RM.Ω →+* Om C.Z) (φ (a0 * x)) = a0 * x := eq.symm_apply_apply _
      rwa [this] at h1
    · have : bb C.Z = 0 := dif_neg hZ
      rw [this, mul_zero]
      exact zero_mem _)
  exact ⟨g, hg, by rw [hgv Z, hbb, hx]⟩

end GlobalTheory.CompanionTheory.Ar.Plug.BirEx

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug.BirEx

theorem bir_of_origin (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (hC : CompLaws U h e) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (nu : Top.Wt (CMType H) (Dw.p + Dw.q)) (hnu : ∀ r : RootIx Dw, (Fx.n r : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * nu r.1 r.2) (hd1 : Or.Fl.deg = 1) (Z : Comp Xo c) (hb : GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z)) :
    ∃ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) ∧ BirOn h Z g := by
  classical
  letI := Small.cstAlg Or
  obtain ⟨φ, P, t, hP, hbor, hrk⟩ := GlobalTheory.T.comp_laws_root_model_relay E H Dw l Xo c r U h e hC Y S RM Sys Fx Or Fr Z hb
  have hφs : Function.Surjective φ := surjective_of_finrank_one φ.toRingHom (hrk.trans hd1)
  have hgs : Function.Surjective Or.g := surjective_of_finrank_one _ (Or.g_deg.trans hd1)
  obtain ⟨n₀, N₀, hn₀, hN₀, hs0, hs0m⟩ := GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model E H Dw l Xo c (𝓞 c.F) _ Y S RM Sys
    Fx Or nu hnu
  set s₀ : RM.Ω := (N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r with hs₀
  let u : GlobalTheory.AllWt.Weight Dw := fun τ i => Fx.n (τ, i)
  have hkA : (RM.kA : ℝ) = Fx.kA := by exact_mod_cast Or.kA_eq
  have hkpos : (0 : ℝ) < Fx.kA := by rw [← hkA]; exact_mod_cast RM.kA_pos
  have hnone : n₀ none = -(Fx.q' : ℤ) := by
    have := hn₀ none
    have e2 : (RM.coef nu (-1) none : ℝ) = -1 / RM.kA := rfl
    rw [e2, hkA] at this
    have e3 : ((n₀ none : ℤ) : ℝ) = ((-(Fx.q' : ℤ) : ℤ) : ℝ) := by
      rw [this]
      push_cast
      field_simp
    exact_mod_cast e3
  have hsome : ∀ r, n₀ (some r) = -Fx.n r := fun r => by
    have := hn₀ (some r)
    have e2 : (RM.coef nu (-1) (some r) : ℝ) = -nu r.1 r.2 := rfl
    rw [e2] at this
    have e3 : ((n₀ (some r) : ℤ) : ℝ) = ((-Fx.n r : ℤ) : ℝ) := by
      rw [this]
      push_cast
      rw [hnu r]
      push_cast
      ring
    exact_mod_cast e3
  have hdeg : ∀ k, degOf RM u k = (Top.combLine (RM.line 1) n₀).a k + if k = Or.k₀ then (Fx.q' : ℤ) else 0 := fun k => by
    have h1 : degOf RM u k = ∑ r : RootIx Dw, - u r.1 r.2 * RM.xdeg r k := by
      show (∑ j, nOf u j • (RM.line 1 j).a) k = _
      rw [Fintype.sum_option]
      simp only [nOf, zero_smul, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      show _ * (RM.x 1 r).a k = _
      rw [RM.x_deg]
    have h2 : (Top.combLine (RM.line 1) n₀).a k = -(Fx.q' : ℤ) * RM.A.a k + ∑ r : RootIx Dw, - u r.1 r.2 * RM.xdeg r k := by
      show (∑ j, n₀ j • (RM.line 1 j).a) k = _
      rw [Fintype.sum_option, hnone]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hsome r]
      show _ * (RM.x 1 r).a k = _
      rw [RM.x_deg]
    rw [h1, h2]
    by_cases hk : k = Or.k₀
    · subst hk
      rw [Or.A_deg.1, if_pos rfl]
      ring
    · rw [Or.A_deg.2 k hk, if_neg hk]
      ring
  obtain ⟨c', hc'⟩ := Or.𝔐.tie.cover ⟨GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ, specializes_rfl⟩
  have hy0 : RM.y ⟨Or.k₀, c' Or.k₀⟩ ≠ 0 := (Finset.prod_ne_zero_iff.1 hc'.1) _ (Finset.mem_univ _)
  let i₀ : Fin (Fx.m + 1) := Or.ix.symm (c' Or.k₀)
  have hi₀ : Or.ix i₀ = c' Or.k₀ := Or.ix.apply_symm_apply _
  have hyi : ∀ i, RM.y ⟨Or.k₀, Or.ix i⟩ = Or.g (Fx.yf i) := Or.y_eq
  have hyg0 : Or.g (Fx.yf i₀) ≠ 0 := by rw [← hyi, hi₀]; exact hy0
  have hyf0 : Fx.yf i₀ ≠ 0 := fun e' => hyg0 (by rw [e', map_zero])
  let s : Fin (Fx.m + 1) → RM.Ω := fun i => s₀ * (RM.y ⟨Or.k₀, Or.ix i⟩ * RM.y ⟨Or.k₀, Or.ix i₀⟩ ^ (Fx.q' - 1))
  have hsm : ∀ i, s i ∈ chartLatNm RM.y (degOf RM u) 1 := fun i =>
    mul_mem_chartLatNm RM.y _ _ Or.k₀ _ _ Fx.q' Fx.q'_pos hdeg hs0m
  choose fr hfr hfv using fun i => exists_rule_of_frame E H Dw l Xo c Y S RM Sys Fx Or Fr h Z φ P t hP hbor hφs u (s i) (hsm i)
  have hG0 : gaugeT Or t u ≠ 0 := mul_ne_zero (Units.ne_zero _)
    (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (Or.lines r).1)
  have hsi0 : s i₀ ≠ 0 := by
    refine mul_ne_zero hs0 (mul_ne_zero ?_ (pow_ne_zero _ ?_))
    all_goals (rw [hi₀]; exact hy0)
  have hev0 : evC h Z (fr i₀) ≠ 0 := fun e' => by
    have := hfv i₀
    rw [e', map_zero] at this
    exact div_ne_zero hsi0 hG0 this.symm
  have hv : ∀ i, (φ : Om Z →+* RM.Ω) (evC h Z (fr i) / evC h Z (fr i₀)) = Or.g (Fx.yf i / Fx.yf i₀) := fun i => by
    have h1 : (φ : Om Z →+* RM.Ω) (evC h Z (fr i) / evC h Z (fr i₀)) = φ (evC h Z (fr i)) / φ (evC h Z (fr i₀)) := map_div₀ _ _ _
    rw [h1, hfv, hfv, div_div_div_cancel_right₀ hG0, map_div₀, ← hyi, ← hyi]
    have hs0' : s₀ ≠ 0 := hs0
    have hq : RM.y ⟨Or.k₀, Or.ix i₀⟩ ≠ 0 := by rw [hi₀]; exact hy0
    simp only [s]
    field_simp
  have htop := adjoin_eq_top_of_ratios (F := c.F) (φ : Om Z →+* RM.Ω) Or.g hgs Fx.yf Fx.generate i₀ hyf0 _ hv
  refine ⟨(GlobalTheory.AllWt.wtOf Dw u 0).1, Fx.m, fun j => fr (Equiv.swap 0 i₀ j), fun j => ?_, ?_, ?_⟩
  · rw [secZ_eq_allWt]
    have : GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = GlobalTheory.AllWt.exOf Dw u 0 := by
      funext i
      rcases i with _ | x
      · show (0 : ℤ) = (2 : ℤ) * 0
        simp
      · rfl
    rw [this]
    exact hfr _
  · simpa using hev0
  · have hr : (Set.range fun j => evC h Z (fr (Equiv.swap 0 i₀ j)) / evC h Z (fr (Equiv.swap 0 i₀ 0))) =
        Set.range fun i => evC h Z (fr i) / evC h Z (fr i₀) := by
      rw [Equiv.swap_apply_left]
      exact (Equiv.swap 0 i₀).surjective.range_comp (fun i => evC h Z (fr i) / evC h Z (fr i₀))
    rw [hr]
    exact htop

end GlobalTheory.CompanionTheory.Ar.Plug.BirEx

namespace GlobalTheory.CompanionTheory.Ar.Plug.BirEx

theorem bir_exists : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (_ : Top.GoodOrigin Y T) (Z : Comp Xo c), ∃ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) ∧ BirOn h Z g := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y _ T o Z
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.tower_components_equiv_of_given E H Dw l Xo c Y T o.toTowerOrigin hG
  obtain ⟨Fr⟩ := GlobalTheory.CompanionTheory.Ar.GenEx.exists_genFrame (o.refOr (κ Z))
  exact bir_of_origin E H Dw l Xo c r U h e hC Y ∅ (o.R (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z)) (o.refOr (κ Z)) Fr T.nu (o.nu_eq (κ Z))
    (o.ref_deg (κ Z)) Z (hκ Z)

end GlobalTheory.CompanionTheory.Ar.Plug.BirEx
