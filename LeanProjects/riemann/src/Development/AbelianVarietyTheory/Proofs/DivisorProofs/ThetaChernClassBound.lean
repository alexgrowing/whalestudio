import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverPullbackThetaDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullRegCoverIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceContDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnConstSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralAddRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralFinsetSumOfPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAcyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingMapGenericDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackDoublingFourthPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMetricLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateWeightDoublingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRiemannFramedChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFramedThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateWeightPeriodChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnPeriodChartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPushforwardLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPushforwardMetricWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTorsionHermitianFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneChainDescentFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvarianceRationalToRealSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticInvariantHermitianFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFormUniversalFlatChernStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensitySiegelPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChernScalingDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalDoublingIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianPrintedStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ThetaRR

theorem naturality : Naturality :=
  ⟨PullbackMain.baseChange, OneVec.oneVector, Gauge.isometryInv_holds, TranslInv.translationInv,
    symplecticInv, TorsionFormCover.coverSum, FlatAcyc.flatAcyclic⟩

theorem univ_torsion (HB : Published.BismutKoehlerTorsion) (g : ℕ) : ∃ t l : ℝ, ∀ s ∈ siegel g,
    ∀ (v : symMat g) (T : Ext (1 + 1)), IsUnivTorsion g s v T →
      T ∅ = t ∧ T Finset.univ = Complex.I * (l * sdens (tauU s) (tauU v) : ℝ) := by
  obtain ⟨F, hF, hU⟩ := GlobalTheory.T.universal_torsion_hermitian_function HB naturality g
  obtain ⟨t, l, h⟩ := GlobalTheory.T.symplectic_invariant_hermitian_function g F hF (GlobalTheory.T.invariance_rational_to_real_symplectic g F hF fun γ hγ s hs v => by
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.universal_torsion_rational_symplectic_invariance HB naturality g γ hγ s hs
    exact (hU s hs v _).1 (h₂ v _ ((hU _ h₁ _ _).2 rfl)))
  exact ⟨t, l, fun s hs v T hT => (hU s hs v T).1 hT ▸ h s hs v⟩

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k}

theorem exists_cubical (hS : IsRegSurf p) (P : PPAS S) {h : VMetric p (omega P.A) P.g}
    (hh : P.IsDualRiemann (1 / 2) h) (hT : P.HasTheta) : ∃ L : HermLB (P.A.hom ≫ p), IsTheta P L.B ∧
      (L.pull (dbl P) (dbl_comp P p)).Isometric (L.pow 4) ∧ FlatCharts P h L := by
  have hA := GlobalTheory.T.abelian_scheme_arith_variety k S p hS P
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_theta_line_bundle k S p hS P hT
  obtain ⟨L, rfl⟩ := GlobalTheory.T.exists_hermitian_metric_line_bundle k _ _ _ hA B hB.1
  obtain ⟨w, hw⟩ := GlobalTheory.T.theta_pullback_doubling_fourth_power k S p hS P L hB
  obtain ⟨u, uc, uj, hu⟩ := GlobalTheory.T.exists_tate_weight_doubling k _ _ _ hA (dbl P) (dbl_comp P p) L w hw
  have hF := GlobalTheory.T.dual_riemann_framed_charts k S p hS P h hh L w hw
  have us : ∀ σ x, CInfAt (u σ) x := fun σ x => by
    obtain ⟨c, τ, ex, j, m, hy, -, hc, hf, hd⟩ := hF σ ⟨x.1 ≫ P.A.hom, by rw [Category.assoc]; exact x.2⟩
    have hm := (GlobalTheory.T.tate_weight_period_chart k S p hS P hA h L hB w hw u uc hu σ c τ ex j m hc hf hd
      (GlobalTheory.T.period_chart_framed_theta k S p hS P h hh L hB σ c τ ex j m hc hf hd)).1
    have hv := c.e.map_source hy
    obtain ⟨z, hz⟩ := (hc.2.2 _ hv).2.2.1 (Over.homMk x.1 (by rw [c.e.left_inv hy]; rfl))
    have e : x = ex (c.e _, z) := Subtype.ext hz
    rw [e]
    refine GlobalTheory.T.smooth_on_period_chart_cover k S p hS P h σ c τ ex hc (u σ) ?_ _ ⟨hv, trivial⟩
    refine ((hd.2.2.2.1.log fun Q hQ => (hd.2.2.2.2.1 Q hQ).ne').sub
      (hm.1.log fun Q hQ => (hm.2.1 Q hQ).ne')).congr fun Q hQ => ?_
    rw [Real.log_mul (hd.2.2.2.2.1 Q hQ).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine ⟨L.raise u us uj, hB, hu.isometric hw us uj, fun σ y => ?_⟩
  obtain ⟨c, τ, ex, j, m, hy, hv, hc, hf, hd⟩ := hF σ y
  obtain ⟨hm, hfl⟩ := GlobalTheory.T.tate_weight_period_chart k S p hS P hA h L hB w hw u uc hu σ c τ ex j m hc hf hd
    (GlobalTheory.T.period_chart_framed_theta k S p hS P h hh L hB σ c τ ex j m hc hf hd)
  refine ⟨c, τ, ex, j, _, hy, hv, hc, ?_, ⟨hd.1, hd.2.1, hd.2.2.1, hm⟩, hfl⟩
  obtain ⟨fr, hfr⟩ := hf
  refine ⟨fr, fun i => ⟨(hfr i).1, fun Q hQ hi => ?_⟩⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (hfr i).2 Q hQ hi
  refine ⟨h₁, h₂, ?_, h₄⟩
  change m Q * Real.exp (-u σ (ex Q)) = _ * Real.exp (-((L.φ σ).φ i (ex Q) + u σ (ex Q)))
  rw [h₃, neg_add, Real.exp_add, mul_assoc]

theorem flagCh2_flat (HA : Published.ArCalc) (HR : Published.ArithRiemannRochAbelian) {g : ℕ} {t l : ℝ}
    (hU : ∀ s ∈ siegel g, ∀ (v : symMat g) (T : Ext (1 + 1)), IsUnivTorsion g s v T →
      T ∅ = t ∧ T Finset.univ = Complex.I * (l * sdens (tauU s) (tauU v) : ℝ))
    [IsIntegral S] (hS : IsRegSurf p) (P : PPAS S) (hg : P.g = g) (hT : P.HasTheta)
    {h : VMetric p (omega P.A) P.g} (H : h.IsCInf) (hh : P.IsDualRiemann (1 / 2) h)
    (fl : Vert.Flag (omega P.A) P.g) {a : ℝ} (ha : VMetric.IsFlagCh2 H fl a) :
    a = (48 * Real.pi * l + 6 * rOne + 3 * t) * gdeg (VMetric.det H) 1 := by
  subst hg
  have hA := GlobalTheory.T.abelian_scheme_arith_variety k S p hS P
  have := hA.isIntegral
  obtain ⟨L, hL, hI, hF⟩ := exists_cubical hS P hh hT
  obtain ⟨M, hM, ⟨ψ⟩⟩ := GlobalTheory.T.theta_pushforward_line_bundle k S p hS P L.B hL
  obtain ⟨φ, h₁, h₂, h₃⟩ := GlobalTheory.T.theta_pushforward_metric_weights k S p hS P h hh L hL M hM ψ
  obtain ⟨hd₁, hd₂⟩ := GlobalTheory.T.doubling_map_generic_degree k S p hS P L.B hL
  obtain ⟨t', ρ, I, -, hρ, hc, hR⟩ := HR k S p hS P.A P.g P.isAb P.smoothDim hA h H L hL.2.2.2.1
    ⟨M, hM, φ, h₁, h₂⟩ ψ h₃
  have key (σ : k →+* ℂ) (y : CxPts p σ) : t' σ y = t ∧ ∃ c : AlgChart p σ 1, y ∈ c.e.source ∧
      ρ σ c y = 8 * Real.pi * l * c.chernDens ((VMetric.det H).φ σ) y := by
    obtain ⟨c, τ, ex, j, m, hy, hv, hp, hf, hd, hfl⟩ := hF σ y
    have hb := c.e.map_source hy
    have hs := hd.1.2.2 _ hb
    have e : tauU (symPart (τ (c.e y))) = τ (c.e y) := by
      ext a b
      change (τ (c.e y) a b + τ (c.e y) b a) / 2 = _
      rw [hs.1.apply a b]
      ring
    obtain ⟨e₁, e₂⟩ := hU _ (by change IsSiegel _; rwa [e]) _ _
      (GlobalTheory.T.torsion_form_universal_flat_chern naturality _ _ _ τ j m hv hd hfl _ hb _ _ (hc σ c τ ex j m hp hf y hy))
    have n : (Finset.univ : Finset (Fin (1 + 1))) ≠ ∅ := by decide
    simp only [curveForm, if_true, if_neg n] at e₁ e₂
    refine ⟨by exact_mod_cast e₁, c, hy, ?_⟩
    rw [GlobalTheory.T.chern_density_siegel_period k S p σ P h H c τ ex hp y hy, ← e]
    have e₃ : (ρ σ c y : ℂ) = ((2 * (l * sdens (tauU (symPart (τ (c.e y))))
        (tauU (fderiv ℂ (fun x => symPart (τ x)) (c.e y) (EuclideanSpace.single 0 1)))) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul]
      refine mul_left_cancel₀ Complex.I_ne_zero ?_
      rw [mul_left_comm, ← e₂]
      push_cast
      ring
    rw [Complex.ofReal_injective e₃]
    field_simp
    ring
  have eI := GlobalTheory.T.top_form_integral_degree k S p hS (VMetric.det H) ρ I _ hρ fun σ y => (key σ y).2
  have et (N : HermLB p) : chInt N 1 t' = t * gdeg N 1 := by
    rw [show t' = fun _ _ => t * 1 from funext fun σ => funext fun y => (key σ y).1.trans (mul_one _).symm]
    simp only [gdeg, chInt, Weight.chernInt_const_mul, mul_finsum]
  have := GlobalTheory.T.arithmetic_functional_quadratic_relations HA k S p hS ⟨M, hM, φ, h₁, h₂⟩ (VMetric.det H) t I a rOne fun N Ψ hΨ => by
    obtain ⟨Φ, hΦ⟩ := ((HA.arExists k _ (P.A.hom ≫ p) _ hA).2 (Fin 3)
      ![L, (VMetric.det H).pull P.A.hom rfl, N.pull P.A.hom rfl]).1
    obtain ⟨z₁, z₂, z₃⟩ := GlobalTheory.T.arithmetic_functional_doubling_isometry HA k _ S (P.A.hom ≫ p) p P.A.hom rfl P.g hA (dbl P) (dbl_comp P p)
      (dbl_hom P) hd₁ hd₂ L _ N hI Φ hΦ
    obtain ⟨r₁, r₂⟩ := hR N Ψ Φ hΨ hΦ
    have r₃ := r₂ fl a ha
    rw [z₁, et, zero_div] at r₁
    rw [z₂, z₃, zero_div, zero_div] at r₃
    constructor
    · linarith
    · linarith
  rw [this, eI]
  ring

theorem isCInf_of_norm [IsIntegral S] (hS : IsRegSurf p) {E : S.Modules} {r : ℕ} {h : VMetric p E r}
    (H : h.IsCInfNorm) : h.IsCInf := by
  have key (q : S ⟶ Sp k) (w : 𝟙 S ≫ p = q) : (h.pull (𝟙 S) w).IsCInf := by
    subst w
    exact VMetric.pull_regCover_isCInf k S p E r h H (.self hS)
  rw [(VMetric.isIsometry_iff _).1 (VMetric.isIsometry_pull_id_comp k S p E r h).1]
  exact (key p _).map _

theorem isCh2Omega_of_flag (HP : CovTop.Hypotheses2) (HD : Published.RegularAlteration)
    (HR : Published.ArithRiemannRochAbelian) {g : ℕ} {t l : ℝ}
    (hU : ∀ s ∈ siegel g, ∀ (v : symMat g) (T : Ext (1 + 1)), IsUnivTorsion g s v T →
      T ∅ = t ∧ T Finset.univ = Complex.I * (l * sdens (tauU s) (tauU v) : ℝ))
    [IsIntegral S] (hS : IsRegSurf p) (P : PPAS S) (hg : P.g = g) (hT : P.HasTheta)
    (fl : Vert.Flag (omega P.A) P.g) :
    P.IsCh2Omega p ((2 * (48 * Real.pi * l + 6 * rOne + 3 * t) + Real.log (2 * Real.pi)) / 2 *
      (P.degOmega p : ℝ)) := by
  obtain ⟨h, hh, hn, hc, hd⟩ := PPAS.exists_isHodge_ch2Omega HP.p4 k S p
    (fun Y q _ hq => RegCoverExists.nonempty_regCover HD k Y q hq) hS.toIsArithVar P
  have H := isCInf_of_norm hS hn
  have h₁ : VMetric.IsFlagCh2 H fl (P.ch2Omega p) := by
    have I := IsometryPullback.isIsometry_symm (VMetric.isIsometry_pull_id_comp k S p _ _ h).1
    obtain ⟨M, e₁, e₂⟩ := IsometryPullback.exists_flagModel_of_eq (h := h) (𝟙 S) (Category.id_comp p) hS rfl
      ((Scheme.Hom.residueDegree_id _).trans_ne one_ne_zero) (H.pull _ _) (fl.ofIso _)
    have e₃ := (e₂ _).1 (hc.2 M)
    rw [e₁, Scheme.Hom.residueDegree_id, Nat.cast_one, one_mul] at e₃
    exact (VMetric.isFlagCh2_ofIso k S p _ _ _ _ _ _ H (H.pull _ _) fl _ I).2 e₃
  have h₂ := GlobalTheory.T.flag_chern_scaling_degree HP.p4 k S p hS _ _ h H fl _ (Real.log (2 * Real.pi)) h₁
  have h₃ := flagCh2_flat HP.p4 HR hU hS P hg hT (H.scale _) hh.flat fl h₂
  have h₄ : gdeg (VMetric.det (H.scale (Real.log (2 * Real.pi)))) 1 = P.degOmega p :=
    (ChernDegree.first_chern_integral_eq_degree k S p hS.toIsArithVar _ _ _ (H.scale _).isCInfNorm).2
  rw [h₄, ← VMetric.firstChernIntegral_eq_degree H, hd] at h₃
  refine ⟨h, hh, ?_⟩
  convert hc using 1
  linarith

theorem exists_const_ch2Omega : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → ∀ g : ℕ, ∃ r : ℝ, ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ P : PPAS S, P.g = g → P.HasTheta → P.IsCh2Omega p (r / 2 * (P.degOmega p : ℝ)) := by
  intro HP HD HR g
  obtain ⟨t, l, hU⟩ := univ_torsion HR.1 g
  refine ⟨2 * (48 * Real.pi * l + 6 * rOne + 3 * t) + Real.log (2 * Real.pi),
    fun k _ S p _ hS P hg hT => ?_⟩
  obtain ⟨h, -, -, ⟨⟨M⟩, -⟩, -⟩ := PPAS.exists_isHodge_ch2Omega HP.p4 k S p
    (fun Y q _ hq => RegCoverExists.nonempty_regCover HD k Y q hq) hS.toIsArithVar P
  obtain ⟨P', φ, hg', hP⟩ := PPAS.exists_pull S M.Y P M.ρ
  obtain ⟨hd, hc⟩ := CoverHodge.degOmega_ch2Omega_cover HP HD k S p hS.toIsArithVar P M.toRegCover P' φ hP
  have fl : Vert.Flag (omega P'.A) P'.g := by
    rw [hg']
    exact M.flag.ofIso (ShFam.Pad.omegaPullIso hP)
  have e := hc _ (isCh2Omega_of_flag HP HD (GlobalTheory.T.arithmetic_riemann_roch_abelian_quoted HP HD HR) hU M.reg P' (hg'.trans hg) (hT.of_isPull hP) fl)
  have hn : (M.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.deg_pos.ne'
  convert e using 1
  rw [hd]
  push_cast
  field_simp

end GlobalTheory.ThetaRR
