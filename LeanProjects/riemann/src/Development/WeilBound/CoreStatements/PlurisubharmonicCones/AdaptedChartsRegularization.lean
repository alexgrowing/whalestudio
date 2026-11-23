import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ProdEqZeroIffCoordDiv
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.SymmetricChartsCutoffFamily

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M.PLAux (chartPush)
open scoped ContDiff

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W)

def IsPiece (S : Finset (Fin D.n)) (g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ) : Prop :=
  AnalyticOnNhd ℂ g (Metric.ball 0 2) ∧ (∀ y ∈ Metric.ball (0 : Fin D.n → ℂ) 2, g y ∈ mcPts (mCoordIdeal D.y)) ∧
    (∀ y ∈ Metric.ball (0 : Fin D.n → ℂ) 2, ∀ y' ∈ Metric.ball (0 : Fin D.n → ℂ) 2, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      g y = torusSmul c (g y') → y = y') ∧
    ∀ y ∈ Metric.ball (0 : Fin D.n → ℂ) 2, g y ∈ D.Bd ↔ y ∈ coordDiv S

private theorem conjVec_mem_mcPts_lemma {K : Type} {κ : K → Type} {P : Ideal (MRing κ)} {z : (Σ k, κ k) → ℂ}
    (hz : z ∈ mcPts P) : conjVec z ∈ mcPts P := by
  simp only [mcPts, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := h1 k
    exact ⟨i, by simpa [conjVec] using hi⟩
  · have h := congrArg (starRingEnd ℂ) (h2 f hf)
    rw [map_zero, MvPolynomial.eval_map, MvPolynomial.hom_eval₂] at h
    rw [MvPolynomial.eval_map]
    convert h using 2
    · exact RingHom.ext_int _ _
    · rfl

private theorem star_mem_ball_lemma_2 {e : ℕ} {y : Fin e → ℂ} (hy : y ∈ Metric.ball (0 : Fin e → ℂ) 2) :
    star y ∈ Metric.ball (0 : Fin e → ℂ) 2 := by
  rw [mem_ball_zero_iff] at hy ⊢
  rw [pi_norm_lt_iff (by norm_num)] at hy ⊢
  intro i
  simpa [Pi.star_apply, Complex.star_def, Complex.norm_conj] using hy i

private theorem conjVec_conjVec_lemma_3 {K : Type} {κ : K → Type} (z : (Σ k, κ k) → ℂ) :
    conjVec (conjVec z) = z := by
  funext p
  simp [conjVec]

private theorem conjVec_torusSmul_lemma_4 {K : Type} {κ : K → Type} (c : K → ℂ) (z : (Σ k, κ k) → ℂ) :
    conjVec (torusSmul c z) = torusSmul (fun k => starRingEnd ℂ (c k)) (conjVec z) := by
  funext p
  simp [conjVec, torusSmul]

theorem IsPiece.conj {S : Finset (Fin D.n)} {g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ} (h : IsPiece D S g) :
    IsPiece D S fun y => conjVec (g (star y)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (fun y => conjVec (g (star y))) (Metric.ball 0 2) := by
      intro y hy
      have h0 : DifferentiableAt ℂ g (star y) := (h1 _ (star_mem_ball_lemma_2 hy)).differentiableAt
      have h5 := h0.star_star
      rw [star_star] at h5
      exact h5.differentiableWithinAt
    rw [analyticOnNhd_pi_iff]
    intro p
    exact ReciprocityTheory.AnForm.Osgood.osgood _ _ _ Metric.isOpen_ball
      (fun y hy => (differentiableAt_pi.1 ((hd y hy).differentiableAt
        (Metric.isOpen_ball.mem_nhds hy)) p).differentiableWithinAt)
  · intro y hy
    exact conjVec_mem_mcPts_lemma (h2 _ (star_mem_ball_lemma_2 hy))
  · intro y hy y' hy' c hc hyy
    have h6 := congrArg conjVec hyy
    rw [conjVec_conjVec_lemma_3, conjVec_torusSmul_lemma_4, conjVec_conjVec_lemma_3] at h6
    have h7 := h3 _ (star_mem_ball_lemma_2 hy) _ (star_mem_ball_lemma_2 hy') _
      (fun k => by simpa using hc k) h6
    simpa using congrArg star h7
  · intro y hy
    constructor
    · intro hm
      have h8 := D.bd_conj _ hm
      rw [conjVec_conjVec_lemma_3, h4 _ (star_mem_ball_lemma_2 hy)] at h8
      obtain ⟨i, hi, hi0⟩ := h8
      exact ⟨i, hi, by simpa using hi0⟩
    · intro hm
      apply D.bd_conj
      rw [h4 _ (star_mem_ball_lemma_2 hy)]
      obtain ⟨i, hi, hi0⟩ := hm
      exact ⟨i, hi, by simp [hi0]⟩

theorem isPiece_chart {S : Finset (Fin D.n)} {a : Fin D.nCharts} {t₀ : Fin D.n → ℂ} {ε : ℝ} (h₀ : ‖t₀‖ ≤ 1 / 2)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hsep : ∀ i : Fin D.n, (i : ℕ) < (D.chart a).a → t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖)
    (hS : ∀ i, i ∈ S ↔ (i : ℕ) < (D.chart a).a ∧ t₀ i = 0) :
    IsPiece D S fun y => (D.chart a).γ (t₀ + (ε : ℂ) • y) := by
  have hmem : ∀ y ∈ Metric.ball (0 : Fin D.n → ℂ) 2,
      t₀ + (ε : ℂ) • y ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := by
    intro y hy
    rw [mem_ball_zero_iff] at hy ⊢
    have hn : ‖(ε : ℂ) • y‖ = ε * ‖y‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε.le]
    have hy0 := norm_nonneg y
    calc ‖t₀ + (ε : ℂ) • y‖ ≤ ‖t₀‖ + ‖(ε : ℂ) • y‖ := norm_add_le _ _
      _ < 1 := by rw [hn]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    have ha : AnalyticAt ℂ (fun y : Fin D.n → ℂ => t₀ + (ε : ℂ) • y) y := by fun_prop
    have hg : AnalyticAt ℂ (D.chart a).γ (t₀ + (ε : ℂ) • y) :=
      (D.chart a).analytic _ (hmem y hy)
    exact hg.comp_of_eq ha rfl
  · intro y hy
    exact (D.chart a).mem _ (hmem y hy)
  · intro y hy y' hy' c hc hyy
    have h1 := (D.chart a).injective _ (hmem y hy) _ (hmem y' hy') c hc hyy
    have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have h2 : (ε : ℂ) • y = (ε : ℂ) • y' := add_left_cancel h1
    exact smul_right_injective _ hε0 h2
  · intro y hy
    rw [(D.chart a).boundary _ (hmem y hy)]
    constructor
    · rintro ⟨i, hi, h0⟩
      have h0' : t₀ i + (ε : ℂ) * y i = 0 := h0
      by_cases ht : t₀ i = 0
      · refine ⟨i, (hS i).2 ⟨hi, ht⟩, ?_⟩
        rw [ht, zero_add] at h0'
        exact (mul_eq_zero.1 h0').resolve_left (by exact_mod_cast hε.ne')
      · exfalso
        have h3 := hsep i hi ht
        have h4 : t₀ i = -((ε : ℂ) * y i) := eq_neg_of_add_eq_zero_left h0'
        have h5 : ‖t₀ i‖ = ε * ‖y i‖ := by
          rw [h4, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
        have h6 : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
        have h7 : ‖y‖ < 2 := mem_ball_zero_iff.1 hy
        nlinarith
    · rintro ⟨i, hiS, hy0⟩
      obtain ⟨hi, ht⟩ := (hS i).1 hiS
      exact ⟨i, hi, by simp [ht, hy0]⟩

variable (M : XModel D) (P : PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n))

private theorem coordDiv_update_lemma_5 {e : ℕ} (T : Finset (Fin e)) (i : Fin e) :
    Function.update (fun _ : Fin e => (1/2 : ℂ)) i 0 ∈ coordDiv T ↔ i ∈ T := by
  constructor
  · rintro ⟨i', hi', h0⟩
    by_cases h : i' = i
    · exact h ▸ hi'
    · rw [Function.update_of_ne h] at h0
      norm_num at h0
  · intro hi
    exact ⟨i, hi, by simp⟩

private theorem update_mem_ball_lemma_6 {e : ℕ} (i : Fin e) :
    Function.update (fun _ : Fin e => (1/2 : ℂ)) i 0 ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
  intro i'
  by_cases h : i' = i
  · subst h
    simp
  · rw [Function.update_of_ne h]
    norm_num

private theorem isPiece_of_adapted_lemma_7 (hA : Adapted M P S) (j : Fin P.N)
    (hT : (P.chart j).target = Metric.ball 0 1) {T : Finset (Fin D.n)}
    {g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ} (hg : IsPiece D T g)
    (hsym : ∀ y ∈ (P.chart j).target, (P.chart j).symm y = M.proj (g y)) : IsPiece D (S j) g := by
  have key : ∀ y ∈ Metric.ball (0 : Fin D.n → ℂ) 1, (y ∈ coordDiv (S j) ↔ y ∈ coordDiv T) := by
    intro y hy
    have hy1 : y ∈ (P.chart j).target := by rw [hT]; exact hy
    have hy2 : y ∈ Metric.ball (0 : Fin D.n → ℂ) 2 := Metric.ball_subset_ball (by norm_num) hy
    have hsrc : M.proj (g y) ∈ (P.chart j).source := by
      rw [← hsym y hy1]
      exact (P.chart j).map_target hy1
    have h1 := hA j (g y) (hg.2.1 y hy2) hsrc
    rw [← hsym y hy1, (P.chart j).right_inv hy1, hg.2.2.2 y hy2] at h1
    exact h1.symm
  have hST : S j = T := by
    ext i
    have h2 := key _ (update_mem_ball_lemma_6 i)
    rwa [coordDiv_update_lemma_5, coordDiv_update_lemma_5] at h2
  rw [hST]
  exact hg

theorem exists_piece (hA : Adapted M P S) (hF : FromSnc M P) (j : Fin P.N) :
    ∃ g, IsPiece D (S j) g ∧ ∀ y ∈ (P.chart j).target, (P.chart j).symm y = M.proj (g y) := by
  obtain ⟨hT, a, t₀, ε, h₀, hε, hε', hsep, hcase⟩ := hF j
  have hP := isPiece_chart D
    (S := Finset.univ.filter (fun i : Fin D.n => (i : ℕ) < (D.chart a).a ∧ t₀ i = 0))
    h₀ hε hε' hsep (fun i => by simp)
  rcases hcase with hc | hc
  · exact ⟨_, isPiece_of_adapted_lemma_7 D M P S hA j hT hP hc, hc⟩
  · exact ⟨_, isPiece_of_adapted_lemma_7 D M P S hA j hT (IsPiece.conj D hP) hc, hc⟩

private theorem contDiffAt_push_lemma_8 {T : Finset (Fin D.n)} {g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ}
    (hg : IsPiece D T g) (k : Fin P.N) {b : (Fin D.n → ℂ) → ℝ} (hbc : IsCompact (tsupport b))
    (hbm : tsupport b ⊆ P.chartMid k) (hsm : M.atlas.SmoothOn (P.mid k) (chartPush (P.chart k) b))
    {y₀ : Fin D.n → ℂ} (hy₀ : y₀ ∈ Metric.ball (0 : Fin D.n → ℂ) 2) :
    ContDiffAt ℝ ∞ (fun y => chartPush (P.chart k) b (M.proj (g y))) y₀ := by
  have hmemev : ∀ᶠ v in 𝓝 y₀, g v ∈ mcPts (mCoordIdeal D.y) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy₀) hg.2.1
  by_cases h : M.proj (g y₀) ∈ P.mid k
  · exact contDiffAt_smoothOn_proj D M (P.isOpen_mid k) hsm (hg.1 y₀ hy₀) hmemev h
  · have hpc : ContinuousAt (fun y => M.proj (g y)) y₀ :=
      ((M.cont _ (hg.2.1 y₀ hy₀)).tendsto).comp
        (tendsto_nhdsWithin_iff.2 ⟨(hg.1 y₀ hy₀).continuousAt, hmemev⟩)
    have hbt : tsupport b ⊆ (P.chart k).target := hbm.trans Set.inter_subset_left
    have hKc : IsCompact ((P.chart k).symm '' tsupport b) :=
      hbc.image_of_continuousOn ((P.chart k).continuousOn_symm.mono hbt)
    have hKm : (P.chart k).symm '' tsupport b ⊆ P.mid k := by
      rintro _ ⟨t, ht, rfl⟩
      have h1 := hbm ht
      simp only [GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartMid, Set.mem_inter_iff,
        Set.mem_preimage] at h1
      exact h1.2
    have hev : ∀ᶠ y in 𝓝 y₀, M.proj (g y) ∉ (P.chart k).symm '' tsupport b :=
      hpc.preimage_mem_nhds (hKc.isClosed.isOpen_compl.mem_nhds (fun hm => h (hKm hm)))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    show chartPush (P.chart k) b (M.proj (g y)) = 0
    unfold chartPush
    by_cases hys : M.proj (g y) ∈ (P.chart k).source
    · rw [Set.indicator_of_mem hys]
      by_contra hne
      exact hy ⟨P.chart k (M.proj (g y)), subset_tsupport _ hne, (P.chart k).left_inv hys⟩
    · exact Set.indicator_of_notMem hys _

theorem exists_local_term (hA : Adapted M P S) {T : Finset (Fin D.n)} {g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ}
    (hg : IsPiece D T g) (k : Fin P.N) {b : (Fin D.n → ℂ) → ℝ} (hbc : IsCompact (tsupport b))
    (hbt : tsupport b ⊆ (P.chart k).target) {y₀ : Fin D.n → ℂ} (hy₀ : y₀ ∈ Metric.ball (0 : Fin D.n → ℂ) 2) :
    ∃ q : (Fin D.n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv T →
      chartPush (P.chart k) b (M.proj (g y)) * ∑ i ∈ S k, Real.log (‖P.chart k (M.proj (g y)) i‖ ^ 2)⁻¹ =
        chartPush (P.chart k) b (M.proj (g y)) * (∑ i ∈ T, Real.log (‖y i‖ ^ 2)⁻¹ + q y) := by
  set e := P.chart k with he
  have hmemev : ∀ᶠ v in 𝓝 y₀, g v ∈ mcPts (mCoordIdeal D.y) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy₀) hg.2.1
  have hpc : ContinuousAt (fun y => M.proj (g y)) y₀ :=
    ((M.cont _ (hg.2.1 y₀ hy₀)).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨(hg.1 y₀ hy₀).continuousAt, hmemev⟩)
  have hKc : IsCompact (e.symm '' tsupport b) :=
    hbc.image_of_continuousOn (e.continuousOn_symm.mono hbt)
  have hF : ∀ x, chartPush e b x ≠ 0 → x ∈ e.symm '' tsupport b := by
    intro x hx
    unfold chartPush at hx
    by_cases hxs : x ∈ e.source
    · rw [Set.indicator_of_mem hxs] at hx
      exact ⟨e x, subset_tsupport _ hx, e.left_inv hxs⟩
    · rw [Set.indicator_of_notMem hxs] at hx
      exact absurd rfl hx
  by_cases h : M.proj (g y₀) ∈ e.symm '' tsupport b
  · obtain ⟨t, ht, hte⟩ := h
    have hs : M.proj (g y₀) ∈ e.source := by
      rw [← hte]
      exact e.map_target (hbt ht)
    have hΦ : AnalyticAt ℂ (fun y => e (M.proj (g y))) y₀ :=
      analyticAt_proj D M (P.compat k) (hg.1 y₀ hy₀) hmemev hs
    have hU : Metric.ball (0 : Fin D.n → ℂ) 2 ∩ (fun y => M.proj (g y)) ⁻¹' e.source ∈ 𝓝 y₀ :=
      Filter.inter_mem (Metric.isOpen_ball.mem_nhds hy₀) (hpc.preimage_mem_nhds (e.open_source.mem_nhds hs))
    have hinj : Set.InjOn (fun y => e (M.proj (g y)))
        (Metric.ball (0 : Fin D.n → ℂ) 2 ∩ (fun y => M.proj (g y)) ⁻¹' e.source) := by
      intro y hy y' hy' hyy
      have h1 : M.proj (g y) = M.proj (g y') := e.injOn hy.2 hy'.2 hyy
      obtain ⟨c, hc, hcz⟩ := (M.fibre _ (hg.2.1 y hy.1) _ (hg.2.1 y' hy'.1)).1 h1
      exact (hg.2.2.1 y' hy'.1 y hy.1 c hc hcz).symm
    have hdiv : ∀ᶠ y in 𝓝 y₀, (y ∈ coordDiv T ↔ e (M.proj (g y)) ∈ coordDiv (S k)) := by
      filter_upwards [hU] with y hy
      exact (hg.2.2.2 y hy.1).symm.trans (hA k (g y) (hg.2.1 y hy.1) hy.2)
    obtain ⟨q, hq, hqev⟩ := exists_smooth_log_diff hΦ hU hinj hdiv
    refine ⟨q, hq, ?_⟩
    filter_upwards [hqev] with y hy hyT
    exact congrArg (fun s => chartPush e b (M.proj (g y)) * s) (hy hyT)
  · have hev : ∀ᶠ y in 𝓝 y₀, M.proj (g y) ∉ e.symm '' tsupport b :=
      hpc.preimage_mem_nhds (hKc.isClosed.isOpen_compl.mem_nhds h)
    refine ⟨0, contDiffAt_const, ?_⟩
    filter_upwards [hev] with y hy _
    have h0 : chartPush e b (M.proj (g y)) = 0 := by
      by_contra hne
      exact hy (hF _ hne)
    rw [h0, zero_mul, zero_mul]

end

open ReciprocityTheory.AnForm.M.PLAux (chartPush) in
theorem adapted_charts_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), Adapted M P S → FromSnc M P → ∃ (r : M.Xc → ℝ) (f : Fin P.N → (Fin D.n → ℂ) → ℝ) (Bf : ℝ), (∀ z ∈ D.Xo, 1 ≤ r (M.proj z)) ∧ (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) (P.chart j).target ∧ ∀ y ∈ (P.chart j).target, |f j y| ≤ Bf) ∧ ∀ j, ∀ y ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j), r ((P.chart j).symm y) = Real.exp 1 + f j y + ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M P S hA hF
  choose b hb using fun j => exists_bumps P j
  obtain ⟨C, hC⟩ := cutoff_of_bumps P b (fun j => (hb j).1) (fun j => (hb j).2.1)
    (fun j x hx => (hb j).2.2.1 _ ⟨x, subset_closure hx, rfl⟩) (fun j => (hb j).2.2.2.1)
    (fun j => (hb j).2.2.2.2)
  have hsm : ∀ k, M.atlas.SmoothOn (P.mid k) (chartPush (P.chart k) (b k)) := by
    intro k
    unfold ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn
    intro a
    exact ((hC.smooth k a).add (contDiffOn_const (c := (1 : ℝ)))).congr (fun y _ => by simp)
  obtain ⟨β, hβ⟩ : ∃ β : Fin P.N → M.Xc → ℝ, β = fun k => chartPush (P.chart k) (b k) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin P.N → M.Xc → ℝ,
      L = fun k x => ∑ i ∈ S k, Real.log (‖P.chart k x i‖ ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : M.Xc → ℝ,
      r = fun x => Real.exp 1 + (∑ k, β k x * L k x) / ∑ k, β k x := ⟨_, rfl⟩
  have hβ0 : ∀ k x, 0 ≤ β k x := by
    intro k x
    rw [hβ]
    exact Set.indicator_nonneg (fun y _ => ((hb k).2.1 _).1) x
  have hB1 : ∀ x, 1 ≤ ∑ k, β k x := by
    intro x
    obtain ⟨j, hj⟩ := P.cover x
    have hxs : x ∈ (P.chart j).source :=
      P.closure_mid j (subset_closure (P.closure_inner j (subset_closure hj)))
    have h1 : β j x = 1 := by
      rw [hβ]
      show (P.chart j).source.indicator (b j ∘ P.chart j) x = 1
      rw [Set.indicator_of_mem hxs]
      exact (hb j).2.2.1 _ ⟨x, subset_closure hj, rfl⟩
    calc (1 : ℝ) = β j x := h1.symm
      _ ≤ ∑ k, β k x := Finset.single_le_sum (fun k _ => hβ0 k x) (Finset.mem_univ j)
  have hβL : ∀ k x, 0 ≤ β k x * L k x := by
    intro k x
    by_cases hxs : x ∈ (P.chart k).source
    · refine mul_nonneg (hβ0 k x) ?_
      rw [hL]
      beta_reduce
      refine Finset.sum_nonneg (fun i _ => ?_)
      have hx1 : ‖P.chart k x‖ < 1 :=
        mem_ball_zero_iff.1 (P.target_subset k ((P.chart k).map_source hxs))
      have hi : ‖P.chart k x i‖ ≤ 1 := (norm_le_pi_norm _ i).trans hx1.le
      rw [Real.log_inv]
      exact neg_nonneg.2 (Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) hi))
    · have h0 : β k x = 0 := by
        rw [hβ]
        show (P.chart k).source.indicator (b k ∘ P.chart k) x = 0
        exact Set.indicator_of_notMem hxs _
      rw [h0, zero_mul]
  have key : ∀ j, ∃ F : (Fin D.n → ℂ) → ℝ, ∃ Cj : ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (P.chart j).target ∧
      (∀ y ∈ (P.chart j).target, |F y| ≤ Cj) ∧
      ∀ y ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j),
        r ((P.chart j).symm y) = Real.exp 1 + F y + ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ := by
    intro j
    obtain ⟨g, hg, hgs⟩ := exists_piece D M P S hA hF j
    obtain ⟨E, hE⟩ : ∃ E : (Fin D.n → ℂ) → ℝ, E = fun y =>
        (∑ k, β k (M.proj (g y)) * L k (M.proj (g y))) / (∑ k, β k (M.proj (g y))) -
          ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ := ⟨_, rfl⟩
    have hloc : ∀ y₀ ∈ Metric.ball (0 : Fin D.n → ℂ) 2, ∃ q : (Fin D.n → ℂ) → ℝ,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q y₀ ∧
          ∀ᶠ y in 𝓝 y₀, y ∉ ReciprocityTheory.AnForm.A.coordDiv (S j) → E y = q y := by
      intro y₀ hy₀
      choose q hq hqev using fun k => exists_local_term D M P S hA hg k (hb k).2.2.2.1
        ((hb k).2.2.2.2.trans Set.inter_subset_left) hy₀
      have hc : ∀ k, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => β k (M.proj (g y))) y₀ := by
        intro k
        rw [hβ]
        exact contDiffAt_push_lemma_8 D M P hg k (hb k).2.2.2.1 (hb k).2.2.2.2 (hsm k) hy₀
      refine ⟨fun y => (∑ k, β k (M.proj (g y)) * q k y) / (∑ k, β k (M.proj (g y))), ?_, ?_⟩
      · exact (ContDiffAt.sum fun k _ => (hc k).mul (hq k)).div (ContDiffAt.sum fun k _ => hc k)
          (ne_of_gt (lt_of_lt_of_le zero_lt_one (hB1 _)))
      · filter_upwards [Filter.eventually_all.2 hqev] with y hy hyT
        have hcl : ∀ k, β k (M.proj (g y)) * L k (M.proj (g y)) =
            β k (M.proj (g y)) * (∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ + q k y) := fun k => by
          rw [hβ, hL]
          exact hy k hyT
        have hB := hB1 (M.proj (g y))
        have hB0 : (∑ k, β k (M.proj (g y))) ≠ 0 := by linarith
        rw [hE]
        beta_reduce
        rw [Finset.sum_congr rfl (fun k _ => hcl k)]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        field_simp
        ring
    obtain ⟨F, hFs, hFE⟩ := exists_smooth_glue Metric.isOpen_ball (S j) E hloc
    obtain ⟨Cj, hCj⟩ := (isCompact_closedBall (0 : Fin D.n → ℂ) 1).exists_bound_of_continuousOn
      (hFs.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num)))
    refine ⟨F, Cj, hFs.mono (fun y hy => Metric.ball_subset_ball (by norm_num) (P.target_subset j hy)),
      fun y hy => ?_, fun y hy => ?_⟩
    · have h1 := hCj y (Metric.ball_subset_closedBall (P.target_subset j hy))
      rwa [Real.norm_eq_abs] at h1
    · have hy1 : y ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := P.target_subset j hy.1
      have hy2 : y ∈ Metric.ball (0 : Fin D.n → ℂ) 2 := Metric.ball_subset_ball (by norm_num) hy1
      have h1 := hFE y hy2 hy.2
      rw [hE] at h1
      beta_reduce at h1
      rw [hgs y hy.1, hr]
      beta_reduce
      linarith
  choose F Cb hFs hFb hFr using key
  refine ⟨r, F, ∑ j, |Cb j|, ?_, ?_, ?_⟩
  · intro z _
    rw [hr]
    beta_reduce
    have h1 := Real.add_one_le_exp 1
    have h2 : 0 ≤ (∑ k, β k (M.proj z) * L k (M.proj z)) / ∑ k, β k (M.proj z) :=
      div_nonneg (Finset.sum_nonneg fun k _ => hβL k _) (le_trans zero_le_one (hB1 _))
    linarith
  · intro j
    refine ⟨hFs j, fun y hy => (hFb j y hy).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun j => |Cb j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  · intro j y hy
    exact hFr j y hy

end LevelTowerAlt
