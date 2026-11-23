import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchA
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquivStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.RA

open GlobalTheory.CompanionTheory.Ar.Rec.FinRd
open GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest (hasVal_unique)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

theorem root_val {Fr : Small.GenFrame Or} {A : Subring RM.Ω} (hG : GoodRing Fr A) {z : (Σ k, RM.ι k) → ℂ}
    (hz : z ∈ Small.ptsOver ℂ (mCoordIdeal RM.y)) (ev : A →+* ℂ)
    (hev : ∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) {zC : Sp ℂ ⟶ Or.𝔐.X}
    (hc : CoordsAt Or.𝔐.ξ RM.y zC z) (hI : Or.𝔐.Interior zC) (ρ : RootIx Dw) {ν : ℝ}
    (hν : Or.𝔐.M.IsGrNorm Or.𝔐.t.PP.L (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1) (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1)
      (HodgeCpt.rootIdx Dw ρ).2 zC 1 ν) :
    (∃ w : ℂ, Small.HasVal RM.y (RM.xdeg ρ) (Or.e ρ)⁻¹ z w ∧
      ‖w‖ = ν ^ HodgeCpt.rootSgn Dw ρ * (Or.sing ρ).h z) ∧
    (Or.sing ρ).h (fun p => starRingEnd ℂ (z p)) = (Or.sing ρ).h z := by
  have hS := Or.hodge ρ zC z hc hI _ _ hν
  obtain ⟨ch, hch⟩ := hS.exists_chart
  obtain ⟨u, hu, eu⟩ := hS.2.2 ch hch
  constructor
  · have hy : ∀ k, RM.y ⟨k, ch k⟩ ≠ 0 := fun k => (hc.2 k (ch k) (IsUnit.mk0 _ (hch k))).1
    have hm := (hG.2.2.1 ρ ch hy).2
    have h1 := hev ⟨_, hm⟩
    have h2 := valAt_of_hasVal hz (Or.𝔐.all _) hc h1
    rw [one_zpow, one_div, Or.sing_deg] at hu
    rw [CxVal.unique h2 hu] at h1
    have h3 := hv_mul h1 (hv_mono hz ch hy hch (RM.xdeg ρ))
    have hM : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
    refine ⟨_, by
      convert h3 using 1
      · rw [zero_add]
      · show _ = (_ * _)⁻¹ * _
        rw [mul_inv, mul_right_comm, inv_mul_cancel₀ hM, one_mul], ?_⟩
    rw [eu, norm_mul, norm_prod, Or.sing_deg]
    simp only [norm_zpow]
  · have hI' : Or.𝔐.Interior (HodgeLine.cj zC) := by
      unfold HodgeCpt.Interior
      rw [HodgeLine.centre_cj]
      exact hI
    have hS' := Or.hodge ρ (HodgeLine.cj zC) _ (HodgeLine.coordsAt_conj hc) hI' _ _
      (HodgeLine.isGrNorm_conj Or.𝔐.t Or.𝔐.M _ hν)
    obtain ⟨u', hu', eu'⟩ := hS'.2.2 ch fun k => (map_ne_zero _).2 (hch k)
    rw [CxVal.unique hu' (HodgeLine.valAt_conj hu)] at eu'
    simp only [Complex.norm_conj, RCLike.norm_conj] at eu'
    exact mul_left_cancel₀ (zpow_pos hν.pos _).ne' (eu'.trans eu.symm)

theorem norm_alg {I : Type} [Fintype I] (T T₀ h K : I → ℝ) (sg ex n : I → ℤ) (hT : ∀ i, 0 < T i)
    (hs : ∀ i, sg i * sg i = 1) (hn : ∀ i, n i = -(sg i * ex i)) :
    (∏ i, T i ^ ex i) * ∏ i, ((K i * (T i * T₀ i)) ^ sg i * h i) ^ n i =
      (∏ i, h i ^ n i) * (∏ i, K i ^ (-ex i)) * ∏ i, T₀ i ^ (-ex i) := by
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : sg i * n i = -ex i := by rw [hn]; linear_combination (-ex i) * hs i
  rw [mul_zpow, ← zpow_mul, e, mul_zpow, mul_zpow, zpow_neg (T i)]
  have := (zpow_pos (hT i) (ex i)).ne'
  field_simp

set_option maxHeartbeats 800000 in
theorem core {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hL : CompLaws U h e) {x : ℝ} (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    {Fr : Small.GenFrame Or} {Z : Comp Xo c} (Rd : Reading Fr h Z) {A : Subring RM.Ω} (hG : GoodRing Fr A)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {z : (Σ k, RM.ι k) → ℂ}
    (hz : z ∈ Small.ptsOver ℂ (mCoordIdeal RM.y)) (ev : A →+* ℂ)
    (hev : ∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x))
    (hcst : ∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) :
    (∀ ρ, (Or.sing ρ).h (fun p => starRingEnd ℂ (z p)) = (Or.sing ρ).h z) ∧
    ∃ k, Over (U σ) (e Z) k ∧ ∃ y ∈ ((U σ).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ),
      (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ,
        ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a *
          ((U σ).X k).pnorm (laZ (U σ) a k) (fun _ => 1) y ∧
        ∀ f ∈ secZ Xo c a, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a
          (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U σ) f k y) := by
  letI := Small.cstAlg Or
  have hU := hL.unf σ hσ
  obtain ⟨zC, ⟨hgen, hc⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.tie ℂ).1 z
    (fun k => (hz.1 k).imp fun _ hi => IsUnit.mk0 _ hi) hz.2
  have hva : ∀ a : A, ValAt Or.𝔐.ξ zC (a : RM.Ω) (ev a) := fun a => valAt_of_hasVal hz hgen hc (hev a)
  obtain ⟨q, φ, yq, hφ, hφA⟩ := hG.2.1
  let ψ₀ : q.R →+* ℂ := ev.comp (φ.toRingHom.codRestrict A hφA)
  let ψ : q.R →ₐ[c.F] CAt σ :=
    { (show q.R →+* CAt σ from ψ₀) with
      commutes' := fun a => by
        have h1 := hev ⟨φ (algebraMap c.F q.R a), hφA _⟩
        have h2 : φ (algebraMap c.F q.R a) = Or.𝔐.cst a := φ.commutes a
        have h3 : Small.HasVal RM.y 0 (φ (algebraMap c.F q.R a)) z (σ a) := by rw [h2]; exact hcst a
        exact hasVal_unique hz h1 h3 }
  obtain ⟨y, hψ⟩ := GlobalTheory.FramedBaseChange.bcEx_all E H Dw l Xo c σ q yq ψ
  obtain ⟨hpt, htan⟩ := @pt_frame E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr ℂ _ σ.toAlgebra zC q φ yq hφ ψ y hψ fun r => hva ⟨φ r, hφA r⟩
  obtain ⟨hI, hpol⟩ := interior_of Or.𝔐 zC (Small.ptF (S := CAt σ) y) hpt.symm
  obtain ⟨k, x₁, t, ht⟩ := hU.2.2.1 y
  obtain ⟨x₀, t₀, ho, h0, hpn⟩ := move_pnorm hσ hU x₁
  have hB' := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) ((U σ).un k x₀) ((U σ).un k x₁) y).2.2.1 t₀ t h0 ht
  have hx0 : 0 < x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hx σ hσ k τ]
    exact norm_pos_iff.2 ((map_ne_zero _).2 ((U σ).X k).ξ0_ne)
  have hnorm : ∀ ρ : RootIx Dw, Or.𝔐.M.IsGrNorm Or.𝔐.t.PP.L (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1)
      (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2 zC 1
      (Real.sqrt (Real.pi * (2 * x)) * (‖toC (t (Small.rootFrameIx Dw ρ) : CAt σ)‖ *
        ‖toC (t₀ (Small.rootFrameIx Dw ρ) : CAt σ)‖)) := fun ρ => by
    have hr := ρ.2.2
    obtain ⟨b, T, hfl, hfr, hT, hTA, hTd⟩ := hG.2.2.2 (HodgeCpt.rootIdx Dw ρ).1 ⟨_, hgen⟩
    have hfr' := isFrameAt_of_tri _ _ b _ T hfl hfr hT (fun i j => HodgeLine.mem_of_valAt (hva ⟨_, hTA i j⟩) hgen)
      fun i => ⟨(hTd i).1, HodgeLine.mem_of_valAt (hva ⟨_, (hTd i).2⟩) hgen⟩
    obtain ⟨Γ, hΓ, hP⟩ := HodgeMetric.GramFrame.exists_gramAt_posDef_of_frame Or.𝔐 zC hgen hpol _ _ hfr'
    obtain ⟨z', v, hz', hv, hIP⟩ := GF.transport Or.𝔐 zC y hpt _ (Small.labelFin Dw (HodgeCpt.rootIdx Dw ρ).1) _
      (htan _) Γ hΓ
    have key := GF.gram hσ hU (by omega) x₀ ho y _ hB' _ _ (Small.mult_labelC Dw (HodgeCpt.rootIdx Dw ρ).1) z' hz' v hv
      Γ hIP (HodgeCpt.rootIdx Dw ρ).2
    have hmul : ‖toC ((t * t₀) (Small.rootFrameIx Dw ρ) : CAt σ)‖ =
        ‖toC (t (Small.rootFrameIx Dw ρ) : CAt σ)‖ * ‖toC (t₀ (Small.rootFrameIx Dw ρ) : CAt σ)‖ :=
      norm_mul (toC (t (Small.rootFrameIx Dw ρ) : CAt σ)) (toC (t₀ (Small.rootFrameIx Dw ρ) : CAt σ))
    rw [hx σ hσ] at key
    exact ⟨hgen, _, Γ, fun _ => rfl, hfr', by simp, hΓ, hP, (key.trans (congrArg _ hmul)).symm⟩
  have hroot := fun ρ => root_val hG hz ev hev hc hI ρ (hnorm ρ)
  refine ⟨fun ρ => (hroot ρ).2, ?_⟩
  choose w hw hwn using fun ρ => (hroot ρ).1
  have htpos : ∀ (t : Ix Dw → (CAt σ)ˣ) j, 0 < ‖toC (t j : CAt σ)‖ := fun t j =>
    norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (t j))
  have hw0 : ∀ ρ, w ρ ≠ 0 := fun ρ => by
    rw [← norm_pos_iff, hwn]
    exact mul_pos (zpow_pos (hnorm ρ).pos _) ((Or.sing ρ).pos z hz.1)
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hsec : ∀ a : WZ E, ∀ f ∈ secZ Xo c a, Small.HasVal RM.y 0 (Fr.rd f) z
      ((∏ j, toC (t j : CAt σ) ^ exZ Dw a j) * rdU (U σ) f k x₁.1) := fun a f hf => by
    have hrd : Fr.rd f = φ (f q yq) := Fr.rd_eq_of_frMap hL.evalWD hf.1 q φ yq hφ
    have hft : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y := ⟨q, ψ, yq, hψ⟩
    have hy : evR Xo c f y = ψ (f q yq) := by
      unfold evR evalAt
      rw [dif_pos hft]
      exact hL.evalWD f hf.1 (CAt σ) _ q _ ψ _ yq y hft.choose_spec.choose_spec.choose_spec hψ
    have hbor : evR Xo c f y = ((∏ i, t i ^ exZ Dw a i : (CAt σ)ˣ) : CAt σ) * evR Xo c f ((U σ).un k x₁) :=
      evalAt_bor_zpow (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1 (exZ Dw a) hf.1
        (fun p t y y' hb => by rw [hf.2 p t y y' hb, Units.coe_prod]) (CAt σ) t _ y (hL.unTest σ hσ k x₁) hft ht
    have h1 := hev ⟨φ (f q yq), hφA _⟩
    have h2 : ev ⟨φ (f q yq), hφA _⟩ = (∏ j, toC (t j : CAt σ) ^ exZ Dw a j) * rdU (U σ) f k x₁.1 := by
      refine (show _ = toC (ψ (f q yq)) from rfl).trans ?_
      rw [← hy, hbor]
      have e1 : rdU (U σ) f k x₁.1 = toC (evR Xo c f ((U σ).un k x₁)) := dif_pos x₁.2
      have e2 : toC ((∏ i, t i ^ exZ Dw a i : (CAt σ)ˣ) : CAt σ) = ∏ j, toC (t j : CAt σ) ^ exZ Dw a j :=
        (Units.coe_prod (M := ℂ) (fun i => t i ^ exZ Dw a i) _).trans
          (Finset.prod_congr rfl fun j _ => Units.val_zpow_eq_zpow_val (α := ℂ) (t j) _)
      rw [e1, ← e2]
      rfl
    rw [hrd, ← h2]
    exact h1
  refine ⟨k, ?_, x₁.1, x₁.2, fun a n' hn => ?_⟩
  · obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.T.compactification_comp_equiv E H Dw l Xo c r U h e hL σ hσ
    refine (hκ1 Z k).2 (by_contra fun hne => ?_)
    have he0 : e Z ∈ secZ Xo c 0 := by
      have h1 := hL.e_sec Z
      rw [← secZ_nat] at h1
      exact h1
    have hex : ∀ i, exZ Dw (0 : WZ E) i = 0 := fun i => by cases i <;> rfl
    have hrd : Fr.rd (e Z) = 1 := by
      rw [Rd.rd_eq 0 (e Z) he0, (hL.e_val Z).1, map_one]
      simp [hex]
    have hv := hsec 0 _ he0
    rw [hrd, (hκ2 Z k hne _ x₁.2).1, mul_zero] at hv
    exact zero_ne_one (hasVal_unique hz hv hv_one)
  have hnone : n' none = 0 := by
    have h1 := hn none
    have h2 : RM.coef (towerWt Dw a) 0 none = 0 := by simp [Top.RootModel.coef]
    rw [h2] at h1
    exact_mod_cast h1
  have hsome : ∀ r, n' (some r) = -(HodgeCpt.rootSgn Dw r * exZ Dw a (Small.rootFrameIx Dw r)) := fun r => by
    have h1 := hn (some r)
    have h2 : RM.coef (towerWt Dw a) 0 (some r) = -towerWt Dw a r.1 r.2 := rfl
    rw [h2, towerWt_root] at h1
    exact_mod_cast h1
  have hdeg : (Top.combLine (RM.line 1) n').a = 0 + ∑ r, n' (some r) • RM.xdeg r := by
    show ∑ j, n' j • (RM.line 1 j).a = _
    rw [Fintype.sum_option, hnone, zero_smul]
    refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
    show n' (some r) • (RM.x 1 r).a = _
    rw [RM.x_deg]
  have hev' : ∀ r, Or.e r ^ (-n' (some r)) = (Or.e r)⁻¹ ^ n' (some r) := fun r => by
    rw [zpow_neg, inv_zpow]
  have hrt : ∀ r ∈ (Finset.univ : Finset (RootIx Dw)), Small.HasVal RM.y (n' (some r) • RM.xdeg r)
      ((Or.e r)⁻¹ ^ n' (some r)) z (w r ^ n' (some r)) := fun r _ =>
    hv_zpow hz (hw r) (inv_ne_zero (Or.lines r).1) (hw0 r) _
  refine ⟨(∏ j, toC (t j : CAt σ) ^ exZ Dw a j) * ∏ r, w r ^ n' (some r), ?_, fun f hf => ?_⟩
  · rw [norm_mul, norm_prod, norm_prod]
    simp only [norm_zpow, hwn]
    rw [prod_exZ Dw a fun j => ‖toC (t j : CAt σ)‖, hpn, lieFacZ_eq Dw hx0, prod_root, prod_root]
    exact norm_alg _ _ _ _ _ _ _ (fun _ => htpos t _) (rootSgn_mul_self Dw) hsome
  · rw [hdeg, mul_right_comm]
    simp only [hev']
    exact hv_mul (hsec a f hf) (hv_prod Finset.univ hrt)

end PositivityTheory.UnitarySelfGeneration.RA
