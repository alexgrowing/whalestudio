import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramAtLocalLog
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ContDiffAtSqrtQuotNormSq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeMetricFramePropertiesStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.SubmatrixGram

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.MuBd

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements Asymptotics
open scoped ComplexOrder

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W)

theorem frame_local (τ : Ψ) (a : Fin D.nCharts) {t₀ : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ)} (hball : t₀ ∈ Metric.ball 0 1)
    {c : (k : K) → J k} {f : Ω} {b : Fin D.N → W τ} (hb : IsFrameOver D.y (D.W τ) c f b)
    (hd : InFrameDomain D.y c f ((D.chart a).γ t₀)) (l : Fin (D.h τ).m)
    (hdl : InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) ((D.chart a).γ t₀)) :
    ∃ S : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → Matrix (Fin D.N) (Fin D.N) ℂ,
      (∀ p q, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => S t p q) t₀) ∧ Function.Injective (S t₀).mulVec ∧
      ∀ᶠ t in 𝓝 t₀, (D.chart a).γ t ∈ D.Xo →
        gramAt (D.h τ) b ((D.chart a).γ t) = (S t)ᴴ * (D.h τ).gram l ((D.chart a).γ t) * S t := by
  classical
  have hγ : ContinuousAt (D.chart a).γ t₀ := ((D.chart a).analytic t₀ hball).continuousAt
  have hz₀ : (D.chart a).γ t₀ ∈ mcPts (mCoordIdeal D.y) := (D.chart a).mem t₀ hball
  have hbAt := HermMetricEq.isFrameAt_of_isFrameOver hb hz₀ hd
  obtain ⟨S, hSr, hSe⟩ := HermMetricEq.exists_coeff ((D.h τ).isFrame l) hz₀ hdl hbAt.1
  choose U hU hUe using fun q =>
    hbAt.2 _ ((HermMetricEq.isFrameAt_of_isFrameOver ((D.h τ).isFrame l) hz₀ hdl).1 q)
  have hSU : S * Matrix.of (fun p q => U q p) = 1 := by
    refine HermMetricEq.coeff_unique ((D.h τ).isFrame l).2.2.2.1 fun q => ?_
    have h1 : ∑ p, (1 : Matrix (Fin D.N) (Fin D.N) Ω) p q • (D.h τ).b l p = (D.h τ).b l q := by
      simp [Matrix.one_apply, ite_smul]
    rw [h1]
    conv_rhs => rw [hUe q]
    simp only [hSe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hval : HermMetricEq.valM D.y S ((D.chart a).γ t₀) *
      HermMetricEq.valM D.y (Matrix.of fun p q => U q p) ((D.chart a).γ t₀) = 1 := by
    ext p q
    have h1 := HermMetricEq.isValueAt_mul (Sz := HermMetricEq.valM D.y S ((D.chart a).γ t₀))
      (Tz := HermMetricEq.valM D.y (Matrix.of fun p q => U q p) ((D.chart a).γ t₀))
      (fun p q => (hSr p q).isValueAt hz₀) (fun p q => (hU q p).isValueAt hz₀) p q
    rw [hSU] at h1
    exact IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz₀ h1 (HermMetricEq.isValueAt_one_matrix p q)
  refine ⟨fun t => HermMetricEq.valM D.y S ((D.chart a).γ t), fun p q =>
    HermMetric.contDiffAt_valAt Metric.isOpen_ball (D.chart a).analytic
      (fun w hw => (D.chart a).mem w hw) hball (hSr p q),
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hval)), ?_⟩
  filter_upwards [Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
    HermMetricEq.eventually_regularAt hγ (hSr p q), HermMetricEq.eventually_inFrameDomain hγ hdl] with t h1 h2 hXo
  exact MuFrameNormLocal.gramAt_eq_of_frame (D.h τ) Set.sdiff_subset hXo h2 h1 hSe

theorem det_pos_pair {j N : ℕ} (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) :
    0 < G.det.re ∧ 0 < (G.submatrix (headIdx hj) (headIdx hj)).det.re :=
  ⟨(Complex.pos_iff.1 hG.det_pos).1,
    (Complex.pos_iff.1 (hG.submatrix (e := headIdx hj) (Fin.castLE_injective hj)).det_pos).1⟩

theorem log_sqrt_quot {j N : ℕ} (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) :
    0 < Real.sqrt (quotNormSq hj G) ∧ Real.log (Real.sqrt (quotNormSq hj G)) =
      (Real.log G.det.re - Real.log (G.submatrix (headIdx hj) (headIdx hj)).det.re) / 2 := by
  obtain ⟨h1, h2⟩ := det_pos_pair hj hG
  unfold quotNormSq
  exact ⟨Real.sqrt_pos.2 (div_pos h1 h2), by rw [Real.log_sqrt (div_pos h1 h2).le, Real.log_div h1.ne' h2.ne']⟩

theorem local_form (Hd : HodgeData D) (a : Fin D.nCharts) {t₀ : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ)} (hball : t₀ ∈ Metric.ball 0 1)
    (l : ∀ τ, Fin (D.h τ).m)
    (hdl : ∀ τ, InFrameDomain D.y ((D.h τ).chart (l τ)) ((D.h τ).fr (l τ)) ((D.chart a).γ t₀)) :
    ∃ (A : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℝ) (S : Ψ → (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → Matrix (Fin D.N) (Fin D.N) ℂ),
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A t₀ ∧
      (∀ τ p q, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => S τ t p q) t₀) ∧
      (∀ τ, Function.Injective (S τ t₀).mulVec) ∧
      ∀ᶠ t in 𝓝 t₀, (D.chart a).γ t ∈ D.Xo →
        (∀ τ, ((S τ t)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ t) * S τ t).PosDef) ∧
        phMu Hd ((D.chart a).γ t) = A t + ∑ τ,
          (Real.log ((S τ t)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ t) * S τ t).det.re -
            Real.log (((S τ t)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ t) * S τ t).submatrix
              (headIdx D.j_le_N) (headIdx D.j_le_N)).det.re) / 2 := by
  obtain ⟨hex, heq, -, -⟩ := GlobalTheory.T.hodge_metric_frame_properties K J II Ψ Ω W D Hd
  have hγ : ContinuousAt (D.chart a).γ t₀ := ((D.chart a).analytic t₀ hball).continuousAt
  have hz₀ : (D.chart a).γ t₀ ∈ mcPts (mCoordIdeal D.y) := (D.chart a).mem t₀ hball
  obtain ⟨d⟩ := hex _ hz₀
  choose S hS hinj hG using fun τ => frame_local D τ a hball (d.adapted τ).1 d.inDom (l τ) (hdl τ)
  obtain ⟨hur, hu0⟩ := MuFrameNormLocal.regularAt_of_isUnitOn hz₀ d.inDom d.unit
  have hγp : ∀ p, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => (D.chart a).γ t p) t₀ :=
    contDiffAt_pi.1 ((((D.chart a).analytic t₀ hball).contDiffAt).restrict_scalars ℝ)
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ‖IndefiniteRowSideFullHecke.LowerBoundFree.valAt D.y d.u ((D.chart a).γ t)‖ *
      ∏ k, ‖(D.chart a).γ t ⟨k, d.c k⟩‖ ^ Hd.aMu k) t₀ :=
    (ContDiffAt.norm ℝ (HermMetric.contDiffAt_valAt Metric.isOpen_ball (D.chart a).analytic
      (fun w hw => (D.chart a).mem w hw) hball hur) hu0).mul (contDiffAt_prod fun k _ =>
        MuWeightChartSmooth.contDiffAt_zpow_of_ne (ContDiffAt.norm ℝ (hγp _) (d.inDom.1 k))
          (norm_ne_zero_iff.2 (d.inDom.1 k)) _)
  have hA0 : ‖IndefiniteRowSideFullHecke.LowerBoundFree.valAt D.y d.u ((D.chart a).γ t₀)‖ *
      ∏ k, ‖(D.chart a).γ t₀ ⟨k, d.c k⟩‖ ^ Hd.aMu k ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.2 hu0) (Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (d.inDom.1 k)))
  refine ⟨_, S, hA.log hA0, hS, hinj, ?_⟩
  filter_upwards [Filter.eventually_all.2 hG, HermMetricEq.eventually_inFrameDomain hγ d.inDom,
    hA.continuousAt.eventually_ne hA0] with t h1 h2 h3 hXo
  have hP : ∀ τ, ((S τ t)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ t) * S τ t).PosDef := fun τ => by
    rw [← h1 τ hXo]
    exact GramAtPosDef.proof D τ _ d.c d.f (d.b τ) hXo (d.adapted τ).1 h2
  refine ⟨hP, ?_⟩
  have e := (heq _ hXo ⟨d.c, d.f, h2, d.b, d.adapted, d.u, d.unit, d.eq⟩).2
  unfold phMu
  rw [e]
  change Real.log (‖valAt D.y d.u ((D.chart a).γ t)‖ * (∏ k, ‖(D.chart a).γ t ⟨k, d.c k⟩‖ ^ Hd.aMu k) *
    ∏ τ, Real.sqrt (quotNormSq D.j_le_N (gramAt (D.h τ) (d.b τ) ((D.chart a).γ t)))) = _
  simp only [fun τ => h1 τ hXo]
  rw [MuFrameNormLocal.valAt_eq_complexPoint_reading hXo.1, Real.log_mul h3
    (Finset.prod_ne_zero_iff.2 fun τ _ => (log_sqrt_quot _ (hP τ)).1.ne'),
    Real.log_prod fun τ _ => (log_sqrt_quot _ (hP τ)).1.ne']
  simp only [fun τ => (log_sqrt_quot D.j_le_N (hP τ)).2]

theorem smooth_off (Hd : HodgeData D) (a : Fin D.nCharts) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => phMu Hd ((D.chart a).γ t)) (offBd D a) := by
  intro t ht
  have hXo := SncPiece.mem_Xo_of_offBd D ht
  choose l hl using fun τ => (D.h τ).cover _ hXo
  obtain ⟨A, S, hA, hS, -, hev⟩ := local_form D Hd a ht.1 l hl
  have hG := fun τ => MuWeightChartSmooth.contDiffAt_sandwich (hS τ) ((D.h τ).smooth a (l τ) t ht.1 hXo (hl τ))
  have hP := (hev.self_of_nhds hXo).1
  refine ContDiffAt.contDiffWithinAt (ContDiffAt.congr_of_eventuallyEq ?_
    ((hev.and ((SncPiece.isOpen_offBd D a).mem_nhds ht)).mono fun s h =>
      (h.1 (SncPiece.mem_Xo_of_offBd D h.2)).2))
  refine hA.add (ContDiffAt.sum fun τ _ => ContDiffAt.div_const (ContDiffAt.sub ?_ ?_) 2)
  · exact ((Complex.reCLM.contDiff.contDiffAt).comp t (MuWeightChartSmooth.contDiffAt_det (hG τ))).log
      (det_pos_pair D.j_le_N (hP τ)).1.ne'
  · exact ((Complex.reCLM.contDiff.contDiffAt).comp t (MuWeightChartSmooth.contDiffAt_det
      (M := fun s => ((S τ s)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ s) * S τ s).submatrix
        (headIdx D.j_le_N) (headIdx D.j_le_N)) fun p q => hG τ _ _)).log (det_pos_pair D.j_le_N (hP τ)).2.ne'

theorem exp_le_logR (a : Fin D.nCharts) {t : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ)} (ht : t ∈ Metric.ball 0 1) :
    Real.exp 1 ≤ (D.chart a).logR t := by
  rw [mem_ball_zero_iff] at ht
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ?_)
  split_ifs
  · rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm t i).trans ht.le))
  · exact le_rfl

theorem bounds (Hd : HodgeData D) (a : Fin D.nCharts) {t₀ : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ)} (ht₀ : ‖t₀‖ ≤ 1 / 2) :
    ∃ C > (0 : ℝ), ∀ᶠ t in 𝓝[offBd D a] t₀, -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧
      phMu Hd ((D.chart a).γ t) ≤ C ∧ ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤
        C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2) := by
  have hball : t₀ ∈ Metric.ball (0 : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ)) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : ContinuousAt (D.chart a).γ t₀ := ((D.chart a).analytic t₀ hball).continuousAt
  choose l hdl ε hε c hc C hC hbd using fun τ => (D.h τ).logBound a t₀ ht₀
  obtain ⟨A, S, hA, hS, hinj, hev⟩ := local_form D Hd a hball l hdl
  set L := 𝓝[offBd D a] t₀ with hL
  set R := (D.chart a).logR with hRdef
  have hl : L ≤ 𝓝 t₀ := nhdsWithin_le_nhds
  have hO : ∀ᶠ t in L, t ∈ offBd D a := self_mem_nhdsWithin
  have hR : ∀ᶠ t in L, Real.exp 1 ≤ R t := hO.mono fun t h => exp_le_logR D a h.1
  have hR1 : ∀ᶠ t in L, 1 ≤ R t ∧ 1 ≤ Real.log (R t) ∧ 1 ≤ Real.exp (R t / 2) := hR.mono fun t h => by
    have h1 : 1 ≤ R t := (Real.one_le_exp zero_le_one).trans h
    exact ⟨h1, (Real.le_log_iff_exp_le (by linarith)).2 h, Real.one_le_exp (by linarith)⟩
  have hone : ∀ {g : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℝ}, (∀ᶠ t in L, 1 ≤ g t) → (fun _ => (1 : ℝ)) =O[L] g := fun {g} h =>
    IsBigO.of_bound 1 (h.mono fun t ht => by
      rw [norm_one, _root_.one_mul]; exact ht.trans (le_abs_self _))
  have hE := hone (hR1.mono fun t h => h.2.2)
  have hev' : ∀ᶠ t in L, _ := (hO.and (hev.filter_mono hl)).mono fun t h =>
    h.2 (SncPiece.mem_Xo_of_offBd D h.1)
  have hq := fun τ => by
    have hdom : ∀ᶠ t in L, InFrameDomain D.y ((D.h τ).chart (l τ)) ((D.h τ).fr (l τ)) ((D.chart a).γ t) :=
      (HermMetricEq.eventually_inFrameDomain hγ (hdl τ)).filter_mono hl
    have hb : ∀ᶠ t in L, _ := ((hO.and hdom).and (hl (Metric.ball_mem_nhds t₀ (hε τ)))).mono fun t h =>
      hbd τ t (mem_ball_iff_norm.1 h.2) (mem_ball_zero_iff.1 h.1.1.1) (SncPiece.mem_Xo_of_offBd D h.1.1) h.1.2
    exact quot_bounds (E := fun t => Real.exp (R t / 2)) D.j_le_N (lt_of_lt_of_le two_pos D.two_le_N) hl hR hE
      (S := S τ) (fun p q => (hS τ p q).of_le (by simp)) (hinj τ)
      (H := fun t => (D.h τ).gram (l τ) ((D.chart a).γ t)) (hc τ) (hC τ)
      (((hO.and hdom).and hb).mono fun t h =>
        ⟨(D.h τ).posDef _ _ (SncPiece.mem_Xo_of_offBd D h.1.1) h.1.2, h.2.1, h.2.2.1⟩)
      (fun p q => (hO.and hdom).mono fun t h =>
        ((D.h τ).smooth a (l τ) t h.1.1 (SncPiece.mem_Xo_of_offBd D h.1) h.2 p q).differentiableAt (by simp))
      (fun p q => IsBigO.of_bound (C τ) (hb.mono fun t h => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact h.2.2 p q))
      (hev'.mono fun t h => h.1 τ)
  have gA : Gr L (fun t => Real.log (R t)) (fun t => R t ^ D.N * Real.exp (R t / 2)) A :=
    Gr.of_contDiffAt hl (hone (hR1.mono fun t h => h.2.1))
      (hone (hR1.mono fun t h => one_le_mul_of_one_le_of_one_le (one_le_pow₀ h.1) h.2.2)) (hA.of_le (by simp))
  have g := gA.add (Gr.sum Finset.univ fun τ _ => (hq τ).1)
  choose B hB using fun τ => (hq τ).2
  obtain ⟨C1, hC1⟩ := g.bdd.bound
  obtain ⟨C2, hC2⟩ := g.der.bound
  obtain ⟨C3, hC3⟩ := ((hA.continuousAt.isBigO_one ℝ).mono hl).bound
  have hnb : ∀ᶠ t in L, ∀ᶠ s in 𝓝 t, _ := ((eventually_eventually_nhdsWithin.2 (hev'.mono fun t h => h.2)).and
    hO).mono fun t h => by
      have h1 := h.1
      rwa [(SncPiece.isOpen_offBd D a).nhdsWithin_eq h.2] at h1
  refine ⟨|C1| + |C2| + |C3| + D.N + ∑ τ, |B τ| + 1, by positivity, ?_⟩
  filter_upwards [hC1, hC2, hC3, hnb, hev', hR1, Filter.eventually_all.2 hB] with t h1 h2 h3 h4 h5 h6 h7
  have hs : 0 ≤ ∑ τ, |B τ| := by positivity
  have hN : (0 : ℝ) ≤ D.N := Nat.cast_nonneg _
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg C2
  have a3 := abs_nonneg C3
  refine ⟨?_, ?_, ?_⟩
  · rw [← h5.2, Real.norm_eq_abs, Real.norm_of_nonneg (by linarith [h6.2.1])] at h1
    refine le_trans (neg_le_neg ?_) (abs_le.1 h1).1
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C1]) (by linarith [h6.2.1])
  · rw [h5.2]
    rw [norm_one, _root_.mul_one, Real.norm_eq_abs] at h3
    have h8 : ∑ τ, (Real.log ((S τ t)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ t) * S τ t).det.re -
        Real.log (((S τ t)ᴴ * (D.h τ).gram (l τ) ((D.chart a).γ t) * S τ t).submatrix
          (headIdx D.j_le_N) (headIdx D.j_le_N)).det.re) / 2 ≤ ∑ τ, |B τ| := by
      refine Finset.sum_le_sum fun τ _ => ?_
      obtain ⟨p1, p2⟩ := det_pos_pair D.j_le_N (h5.1 τ)
      rw [← Real.log_div p1.ne' p2.ne']
      have h9 := (Real.log_le_self (div_pos p1 p2).le).trans (h7 τ)
      linarith [le_abs_self (B τ), abs_nonneg (B τ)]
    linarith [le_abs_self (A t), le_abs_self C3]
  · rw [Filter.EventuallyEq.fderiv_eq h4]
    refine h2.trans ?_
    have hp : 0 ≤ R t ^ D.N * Real.exp (R t / 2) := mul_nonneg (pow_nonneg (by linarith [h6.1]) _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hp, _root_.mul_assoc]
    refine mul_le_mul (by linarith [le_abs_self C2]) (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hp
      (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h6.1 (by linarith)

end LevelTowerAlt.MuBd

theorem LevelTowerAlt.mu_potential_smooth_off_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ a, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => phMu Hd ((D.chart a).γ t)) (offBd D a)) ∧ ∀ a, ∀ t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t₀‖ ≤ 1 / 2 → ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < ε → -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧ ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤ C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd
  refine ⟨LevelTowerAlt.MuBd.smooth_off D Hd, fun a t₀ ht₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := LevelTowerAlt.MuBd.bounds D Hd a ht₀
  obtain ⟨ε, hε, hs⟩ := Metric.mem_nhdsWithin_iff.1 h
  exact ⟨ε, hε, C, hC, fun t ht hd => hs ⟨mem_ball_iff_norm.2 hd, ht⟩⟩
