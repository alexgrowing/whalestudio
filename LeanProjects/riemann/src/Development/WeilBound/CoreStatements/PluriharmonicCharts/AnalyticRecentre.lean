import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystem

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HodgeMetric
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.c_bm_exists_local

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem not_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have := h.2 1 trivial
  simp at this

private theorem fderiv_pi_apply {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Q]
    {G : E → Q → ℂ} {y : E} (hG : DifferentiableAt ℂ G y) (q : Q) (w : E) :
    fderiv ℂ G y w q = fderiv ℂ (fun z => G z q) y w := by
  have h1 : (fun z => G z q) = (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Q => ℂ) q) ∘ G := rfl
  rw [h1, fderiv_comp y (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Q => ℂ) q).differentiableAt hG,
    ContinuousLinearMap.fderiv]
  rfl

theorem imm_chart {P : Ideal (MRing ι)} {D : ℕ} (R : AnLogRes P ⊤ D) (x : R.X) (j : Fin R.A.n) (y : Fin D → ℂ)
    (hyt : y ∈ (R.A.chart j).target) (hxU : (R.A.chart j).symm y ∈ R.U x) (w : Fin D → ℂ) (c : K → ℂ)
    (hc : fderiv ℂ (fun y' => R.lift x ((R.A.chart j).symm y')) y w =
      torusSmul c (R.lift x ((R.A.chart j).symm y))) : w = 0 := by
  classical
  have hx'src : (R.A.chart j).symm y ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hyx' : R.A.chart j ((R.A.chart j).symm y) = y := (R.A.chart j).right_inv hyt
  have hmem := R.mem ((R.A.chart j).symm y) ((R.A.chart j).symm y) (R.mem_U _)
  choose p hp using hmem.1
  have himm := R.immersion ((R.A.chart j).symm y) (not_top _) p hp j hx'src
  rw [hyx'] at himm
  have hdiffq : ∀ q, DifferentiableAt ℂ (fun z => R.lift x ((R.A.chart j).symm z) q) y := fun q =>
    (R.holo x q j y ⟨hyt, hxU⟩).differentiableAt
  have hdiff : DifferentiableAt ℂ (fun z => R.lift x ((R.A.chart j).symm z)) y :=
    differentiableAt_pi.mpr hdiffq
  obtain ⟨c0, hc0, hc0eq⟩ := R.compat x ((R.A.chart j).symm y) ((R.A.chart j).symm y) ⟨hxU, R.mem_U _⟩
  have hb : ∀ k, R.lift x ((R.A.chart j).symm y) ⟨k, p k⟩ ≠ 0 := by
    intro k
    rw [hc0eq]
    exact mul_ne_zero (hc0 k) (hp k)
  have hgq : ∀ q : Σ k, ι k, DifferentiableAt ℂ
      (fun z => R.lift x ((R.A.chart j).symm z) q / R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩) y := by
    intro q
    simp only [div_eq_mul_inv]
    exact (hdiffq q).mul ((hdiffq ⟨q.1, p q.1⟩).inv (hb q.1))
  have hopen : IsOpen ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U ((R.A.chart j).symm y))) :=
    (R.A.chart j).continuousOn_symm.isOpen_inter_preimage (R.A.chart j).open_target
      ((R.isOpen_U x).inter (R.isOpen_U _))
  have hev : (fun z => affCoord p (R.lift x ((R.A.chart j).symm z))) =ᶠ[𝓝 y]
      (fun z => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm z))) := by
    filter_upwards [hopen.mem_nhds ⟨hyt, hxU, R.mem_U _⟩] with z hz
    obtain ⟨c1, hc1, hc1eq⟩ := R.compat x ((R.A.chart j).symm y) _ hz.2
    rw [hc1eq]
    funext q
    simp only [affCoord]
    exact mul_div_mul_left _ _ (hc1 q.1)
  have hker : fderiv ℂ (fun z => affCoord p (R.lift x ((R.A.chart j).symm z))) y =
      fderiv ℂ (fun z => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm z))) y :=
    hev.fderiv_eq
  have hcomp : ∀ r : Σ k, ι k, fderiv ℂ (fun z => R.lift x ((R.A.chart j).symm z) r) y w =
      c r.1 * R.lift x ((R.A.chart j).symm y) r := by
    intro r
    rw [← fderiv_pi_apply hdiff r w, hc]
    rfl
  have hmain : ∀ q : Σ k, ι k,
      fderiv ℂ (fun z => R.lift x ((R.A.chart j).symm z) q / R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩) y w
        = 0 := by
    intro q
    have hbd := hdiffq ⟨q.1, p q.1⟩
    have hbne := hb q.1
    have hg := hgq q
    have hcq := hcomp q
    have hcr := hcomp ⟨q.1, p q.1⟩
    have hbev := hbd.continuousAt.eventually_ne hbne
    have hprod : ((fun z => R.lift x ((R.A.chart j).symm z) q / R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩) *
        (fun z => R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩)) =ᶠ[𝓝 y]
        fun z => R.lift x ((R.A.chart j).symm z) q := by
      filter_upwards [hbev] with z hz
      exact div_mul_cancel₀ _ hz
    have e : fderiv ℂ ((fun z => R.lift x ((R.A.chart j).symm z) q / R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩) *
        (fun z => R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩)) y =
        fderiv ℂ (fun z => R.lift x ((R.A.chart j).symm z) q) y := hprod.fderiv_eq
    rw [fderiv_mul hg hbd] at e
    have e2 := congrArg (fun T => T w) e
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hcq, hcr] at e2
    have h3 : R.lift x ((R.A.chart j).symm y) q / R.lift x ((R.A.chart j).symm y) ⟨q.1, p q.1⟩ *
        (c q.1 * R.lift x ((R.A.chart j).symm y) ⟨q.1, p q.1⟩) = c q.1 * R.lift x ((R.A.chart j).symm y) q := by
      field_simp
    have h4 : R.lift x ((R.A.chart j).symm y) ⟨q.1, p q.1⟩ *
        fderiv ℂ (fun z => R.lift x ((R.A.chart j).symm z) q / R.lift x ((R.A.chart j).symm z) ⟨q.1, p q.1⟩) y w
        = 0 := by
      linear_combination e2 - h3
    exact (mul_eq_zero.mp h4).resolve_left hbne
  have hdiffA : DifferentiableAt ℂ (fun z => affCoord p (R.lift x ((R.A.chart j).symm z))) y :=
    differentiableAt_pi.mpr fun q => hgq q
  have hw : fderiv ℂ (fun z => affCoord p (R.lift x ((R.A.chart j).symm z))) y w = 0 := by
    funext q
    rw [fderiv_pi_apply hdiffA q w]
    exact hmain q
  have hw' : fderiv ℂ (fun z => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm z))) y w = 0 := by
    rw [← hker]
    exact hw
  exact LinearMap.ker_eq_bot'.mp himm w hw'

theorem inj_of_leftInv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : F → E} {x : E} (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g (f x))
    (h : g ∘ f =ᶠ[𝓝 x] id) {v : E} (hv : fderiv ℂ f x v = 0) : v = 0 := by
  have h1 := h.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp x hg hf, fderiv_id] at h1
  have h2 := congrArg (fun A => A v) h1
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.id_apply] at h2
  exact h2.symm

theorem analytic_recentre {n : ℕ} (w₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    AnalyticAt ℂ (recentre w₀ ρ π) t := by
  unfold recentre
  rw [show (fun u : Fin n → ℂ => w₀ + (ρ : ℂ) • u ∘ π) = fun u i => w₀ i + (ρ : ℂ) * u (π i) from by
    funext u i
    simp]
  refine analyticAt_pi_iff.mpr fun i => ?_
  exact analyticAt_const.add (analyticAt_const.mul
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (π i)).analyticAt t))

theorem analytic_uncentre {n : ℕ} (w₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    AnalyticAt ℂ (uncentre w₀ ρ π) t := by
  unfold uncentre
  refine analyticAt_pi_iff.mpr fun i => ?_
  exact analyticAt_const.mul
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (π.symm i)).analyticAt t).sub analyticAt_const)

theorem uncentre_recentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    uncentre t₀ ρ π (recentre t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [recentre, uncentre, h]

theorem recentre_mem_ball {n : ℕ} (w₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) {t : Fin n → ℂ}
    (ht : t ∈ Metric.ball (0 : Fin n → ℂ) 1) : recentre w₀ ρ π t ∈ Metric.ball w₀ ρ := by
  rw [mem_ball_zero_iff] at ht
  have hc : ‖t ∘ π‖ < 1 :=
    (pi_norm_lt_iff one_pos).mpr fun i => lt_of_le_of_lt (norm_le_pi_norm t (π i)) ht
  have h1 : ρ * ‖t ∘ π‖ < ρ := by simpa using mul_lt_mul_of_pos_left hc hρ
  rw [Metric.mem_ball, dist_eq_norm]
  simpa [recentre, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] using h1

theorem exists_perm {n : ℕ} (S : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ j, ((π j : Fin n) : ℕ) < S.card ↔ j ∈ S := by
  classical
  have hc : S.card ≤ n := by simpa using S.card_le_univ
  have h1 : Fintype.card {j : Fin n // j ∈ S} = Fintype.card {j : Fin n // (j : ℕ) < S.card} := by
    rw [Fintype.card_coe, ← Fintype.card_congr (Fin.castLEquiv hc), Fintype.card_fin]
  have h2 : Fintype.card {j : Fin n // ¬ j ∈ S} = Fintype.card {j : Fin n // ¬ (j : ℕ) < S.card} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let e := Fintype.equivOfCardEq h1
  let e' := Fintype.equivOfCardEq h2
  let π : Equiv.Perm (Fin n) := ((Equiv.sumCompl (fun j : Fin n => j ∈ S)).symm.trans
    (e.sumCongr e')).trans (Equiv.sumCompl (fun j : Fin n => (j : ℕ) < S.card))
  refine ⟨π, fun j => ?_⟩
  by_cases hj : j ∈ S
  · have hπ : π j = (e ⟨j, hj⟩ : Fin n) := by
      simp only [π, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hj, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hπ]
    exact iff_of_true (e ⟨j, hj⟩).2 hj
  · have hπ : π j = (e' ⟨j, hj⟩ : Fin n) := by
      simp only [π, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hj, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
    rw [hπ]
    exact iff_of_false (e' ⟨j, hj⟩).2 hj

private theorem analyticAt_lift_chart_symm {P : Ideal (MRing ι)} {n : ℕ} (R : AnLogRes P ⊤ n) (B : FinHolAtlas n R.X)
    (hAB : R.A.Compatible B) (k : Fin B.n) (x₀ : R.X) {v : Fin n → ℂ} (hv : v ∈ (B.chart k).target)
    (hU : (B.chart k).symm v ∈ R.U x₀) : AnalyticAt ℂ (fun v' => R.lift x₀ ((B.chart k).symm v')) v := by
  refine analyticAt_pi_iff.mpr fun q => ?_
  obtain ⟨j0, hj0⟩ := R.A.cover ((B.chart k).symm v)
  have hu : (R.A.chart j0) ((B.chart k).symm v) ∈ (R.A.chart j0).target ∩ (R.A.chart j0).symm ⁻¹' R.U x₀ :=
    ⟨(R.A.chart j0).map_source hj0, by simp [Set.mem_preimage, (R.A.chart j0).left_inv hj0, hU]⟩
  have h1 : AnalyticAt ℂ ((fun y => R.lift x₀ y q) ∘ (R.A.chart j0).symm)
      ((R.A.chart j0) ((B.chart k).symm v)) := R.holo x₀ q j0 _ hu
  have h2 : AnalyticAt ℂ ((R.A.chart j0) ∘ (B.chart k).symm) v := hAB.2 k j0 v ⟨hv, hj0⟩
  have h3 : AnalyticAt ℂ (((fun y => R.lift x₀ y q) ∘ (R.A.chart j0).symm) ∘
      ((R.A.chart j0) ∘ (B.chart k).symm)) v :=
    AnalyticAt.comp (g := (fun y => R.lift x₀ y q) ∘ (R.A.chart j0).symm)
      (f := (R.A.chart j0) ∘ (B.chart k).symm) h1 h2
  refine h3.congr ?_
  filter_upwards [((B.chart k).continuousAt_symm hv).preimage_mem_nhds
    ((R.A.chart j0).open_source.mem_nhds hj0)] with v' hv'
  simp [(R.A.chart j0).left_inv hv']

theorem exists_sncChart {P : Ideal (MRing ι)} {n : ℕ} (R : AnLogRes P ⊤ n) (B : FinHolAtlas n R.X)
    (hAB : R.A.Compatible B) (k : Fin B.n) (w₀ : Fin n → ℂ) (hw₀ : w₀ ∈ (B.chart k).target)
    (Bd : Set ((Σ k, ι k) → ℂ)) (Z : Set R.X) (S : Finset (Fin n))
    (hS : ∀ y ∈ (B.chart k).target, ((B.chart k).symm y ∈ Z ↔ ∃ i ∈ S, y i = 0))
    (hZ : ∀ x₀, ∀ x ∈ R.U x₀, R.lift x₀ x ∈ Bd ↔ x ∈ Z) :
    ∃ (ρ : ℝ) (π : Equiv.Perm (Fin n)) (χ : SncChart P n Bd), 0 < ρ ∧ ρ ≤ 1 / 2 ∧
      (∀ w ∈ Metric.ball w₀ ρ, w ∈ (B.chart k).target ∧ (B.chart k).symm w ∈ R.U ((B.chart k).symm w₀)) ∧
      (∀ t, χ.γ t = R.lift ((B.chart k).symm w₀) ((B.chart k).symm (recentre w₀ ρ π t))) ∧
      ∀ i : Fin n, (i : ℕ) < χ.a → π.symm i ∈ S ∧ w₀ (π.symm i) = 0 := by
  classical
  set x₀ := (B.chart k).symm w₀ with hx₀
  have hW : IsOpen ((B.chart k).target ∩ (B.chart k).symm ⁻¹' R.U x₀) :=
    (B.chart k).continuousOn_symm.isOpen_inter_preimage (B.chart k).open_target (R.isOpen_U x₀)
  have hw₀W : w₀ ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' R.U x₀ := ⟨hw₀, R.mem_U x₀⟩
  obtain ⟨ρ₀, hρ₀, hball₀⟩ := Metric.isOpen_iff.mp hW w₀ hw₀W
  have hev : ∀ᶠ ρ in 𝓝[>] (0:ℝ), ρ < ρ₀ ∧ ρ ≤ 1 / 2 ∧ ∀ i, w₀ i ≠ 0 → ρ < ‖w₀ i‖ := by
    refine ((eventually_lt_nhds hρ₀).and ((eventually_le_nhds (by norm_num : (0:ℝ) < 1 / 2)).and
      (Filter.eventually_all.mpr fun i => ?_))).filter_mono nhdsWithin_le_nhds
    by_cases hi : w₀ i = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd hi h
    · filter_upwards [eventually_lt_nhds (norm_pos_iff.mpr hi)] with ρ h _ using h
  obtain ⟨ρ, ⟨hρρ₀, hρhalf, hρw⟩, hρpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hρ : 0 < ρ := hρpos
  obtain ⟨π, hπ⟩ := exists_perm (S.filter fun i => w₀ i = 0)
  have hballW : ∀ w ∈ Metric.ball w₀ ρ, w ∈ (B.chart k).target ∧ (B.chart k).symm w ∈ R.U x₀ :=
    fun w hw => hball₀ (Metric.ball_subset_ball hρρ₀.le hw)
  have hrec : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, recentre w₀ ρ π t ∈ Metric.ball w₀ ρ :=
    fun t ht => recentre_mem_ball w₀ hρ π ht
  let γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun t => R.lift x₀ ((B.chart k).symm (recentre w₀ ρ π t))
  have hanalytic : AnalyticOnNhd ℂ γ (Metric.ball 0 1) := by
    intro t ht
    obtain ⟨hrt, hrU⟩ := hballW _ (hrec t ht)
    exact (analyticAt_lift_chart_symm R B hAB k x₀ hrt hrU).comp (analytic_recentre w₀ ρ π t)
  have hmemP : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, γ t ∈ mcPts P :=
    fun t ht => R.mem x₀ _ (hballW _ (hrec t ht)).2
  have himm : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (v : Fin n → ℂ),
      (∃ (c : K → ℂ), (fderiv ℂ γ t) v = torusSmul c (γ t)) → v = 0 := by
    rintro t ht v ⟨c, hcv⟩
    obtain ⟨hrt, hrU⟩ := hballW _ (hrec t ht)
    obtain ⟨j0, hj0⟩ := R.A.cover ((B.chart k).symm (recentre w₀ ρ π t))
    have hopen : IsOpen ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (R.A.chart j0).source) :=
      (B.chart k).continuousOn_symm.isOpen_inter_preimage (B.chart k).open_target (R.A.chart j0).open_source
    have hN : {t' | recentre w₀ ρ π t' ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R.A.chart j0).source} ∈ 𝓝 t :=
      (analytic_recentre w₀ ρ π t).continuousAt.preimage_mem_nhds (hopen.mem_nhds ⟨hrt, hj0⟩)
    have hfan : AnalyticAt ℂ (fun t' => R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t'))) t :=
      (hAB.2 k j0 _ ⟨hrt, hj0⟩).comp (analytic_recentre w₀ ρ π t)
    have hyt : R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t)) ∈ (R.A.chart j0).target :=
      (R.A.chart j0).map_source hj0
    have hsymm : (R.A.chart j0).symm (R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t))) =
        (B.chart k).symm (recentre w₀ ρ π t) := (R.A.chart j0).left_inv hj0
    have hxU : (R.A.chart j0).symm (R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t))) ∈ R.U x₀ := by
      rw [hsymm]
      exact hrU
    have hL1 : DifferentiableAt ℂ (fun y => R.lift x₀ ((R.A.chart j0).symm y))
        (R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t))) :=
      differentiableAt_pi.mpr fun q => (R.holo x₀ q j0 _ ⟨hyt, hxU⟩).differentiableAt
    have hγeq : γ =ᶠ[𝓝 t] (fun y => R.lift x₀ ((R.A.chart j0).symm y)) ∘
        (fun t' => R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t'))) := by
      filter_upwards [hN] with t' ht'
      simp only [γ, Function.comp_apply, (R.A.chart j0).left_inv ht'.2]
    have hd : fderiv ℂ γ t v = fderiv ℂ (fun y => R.lift x₀ ((R.A.chart j0).symm y))
        (R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t)))
        (fderiv ℂ (fun t' => R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t'))) t v) := by
      rw [hγeq.fderiv_eq, fderiv_comp t hL1 hfan.differentiableAt]
      rfl
    have hu := imm_chart R x₀ j0 _ hyt hxU
      (fderiv ℂ (fun t' => R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t'))) t v) c
      (by rw [← hd, hcv, hsymm])
    have hmemB : R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t)) ∈
        (R.A.chart j0).target ∩ (R.A.chart j0).symm ⁻¹' (B.chart k).source :=
      ⟨hyt, by rw [Set.mem_preimage, hsymm]; exact (B.chart k).map_target hrt⟩
    have hgan : AnalyticAt ℂ (fun y => uncentre w₀ ρ π (B.chart k ((R.A.chart j0).symm y)))
        (R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t))) :=
      (analytic_uncentre w₀ ρ π _).comp (hAB.1 j0 k _ hmemB)
    have hleft : (fun y => uncentre w₀ ρ π (B.chart k ((R.A.chart j0).symm y))) ∘
        (fun t' => R.A.chart j0 ((B.chart k).symm (recentre w₀ ρ π t'))) =ᶠ[𝓝 t] id := by
      filter_upwards [hN] with t' ht'
      simp only [Function.comp_apply, id, (R.A.chart j0).left_inv ht'.2, (B.chart k).right_inv ht'.1,
        uncentre_recentre w₀ hρ π]
    exact inj_of_leftInv hfan.differentiableAt hgan.differentiableAt hleft hu
  have hinj : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ t' ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (c : K → ℂ),
      (∀ (k : K), c k ≠ 0) → γ t = torusSmul c (γ t') → t = t' := by
    intro t ht t' ht' c hc heq
    obtain ⟨hrt, hrU⟩ := hballW _ (hrec t ht)
    obtain ⟨hrt', hrU'⟩ := hballW _ (hrec t' ht')
    obtain ⟨c1, hc1, hc1eq⟩ := R.compat x₀ ((B.chart k).symm (recentre w₀ ρ π t))
      ((B.chart k).symm (recentre w₀ ρ π t)) ⟨hrU, R.mem_U _⟩
    obtain ⟨c2, hc2, hc2eq⟩ := R.compat x₀ ((B.chart k).symm (recentre w₀ ρ π t'))
      ((B.chart k).symm (recentre w₀ ρ π t')) ⟨hrU', R.mem_U _⟩
    have horb : SameOrbit (R.lift ((B.chart k).symm (recentre w₀ ρ π t)) ((B.chart k).symm (recentre w₀ ρ π t)))
        (R.lift ((B.chart k).symm (recentre w₀ ρ π t')) ((B.chart k).symm (recentre w₀ ρ π t'))) := by
      refine ⟨fun k => (c1 k)⁻¹ * c k * c2 k,
        fun k => mul_ne_zero (mul_ne_zero (inv_ne_zero (hc1 k)) (hc k)) (hc2 k), ?_⟩
      funext p
      have h1p := congrFun hc1eq p
      have h2p := congrFun hc2eq p
      have hep : R.lift x₀ ((B.chart k).symm (recentre w₀ ρ π t)) p =
          c p.1 * R.lift x₀ ((B.chart k).symm (recentre w₀ ρ π t')) p := congrFun heq p
      simp only at h1p h2p ⊢
      rw [h2p, h1p] at hep
      calc R.lift ((B.chart k).symm (recentre w₀ ρ π t)) ((B.chart k).symm (recentre w₀ ρ π t)) p
          = (c1 p.1)⁻¹ * (c1 p.1 *
            R.lift ((B.chart k).symm (recentre w₀ ρ π t)) ((B.chart k).symm (recentre w₀ ρ π t)) p) :=
            (inv_mul_cancel_left₀ (hc1 p.1) _).symm
        _ = (c1 p.1)⁻¹ * c p.1 * c2 p.1 *
            R.lift ((B.chart k).symm (recentre w₀ ρ π t')) ((B.chart k).symm (recentre w₀ ρ π t')) p := by
            rw [hep]
            ring
    have hzz := R.inj _ _ (not_top _) horb
    have hrr : recentre w₀ ρ π t = recentre w₀ ρ π t' := by
      have h := congrArg (B.chart k) hzz
      rwa [(B.chart k).right_inv hrt, (B.chart k).right_inv hrt'] at h
    calc t = uncentre w₀ ρ π (recentre w₀ ρ π t) := (uncentre_recentre w₀ hρ π t).symm
      _ = uncentre w₀ ρ π (recentre w₀ ρ π t') := by rw [hrr]
      _ = t' := uncentre_recentre w₀ hρ π t'
  have hbd : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      γ t ∈ Bd ↔ ∃ (i : Fin n), (i : ℕ) < (S.filter fun i => w₀ i = 0).card ∧ t i = 0 := by
    intro t ht
    obtain ⟨hrt, hrU⟩ := hballW _ (hrec t ht)
    have hnorm : ∀ i, ‖t i‖ < 1 := fun i => lt_of_le_of_lt (norm_le_pi_norm t i) (mem_ball_zero_iff.mp ht)
    have hrec_i : ∀ i, recentre w₀ ρ π t i = w₀ i + (ρ : ℂ) * t (π i) := fun i => by simp [recentre]
    rw [show γ t = R.lift x₀ ((B.chart k).symm (recentre w₀ ρ π t)) from rfl, hZ x₀ _ hrU, hS _ hrt]
    constructor
    · rintro ⟨i, hiS, hi0⟩
      rw [hrec_i] at hi0
      have hw0 : w₀ i = 0 := by
        by_contra hne
        have h1 : ‖w₀ i‖ = ρ * ‖t (π i)‖ := by
          have e : w₀ i = -((ρ : ℂ) * t (π i)) := eq_neg_of_add_eq_zero_left hi0
          rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
        have h2 : ρ * ‖t (π i)‖ < ρ := by simpa using mul_lt_mul_of_pos_left (hnorm (π i)) hρ
        linarith [hρw i hne]
      have ht0 : t (π i) = 0 := by
        rw [hw0, zero_add] at hi0
        exact (mul_eq_zero.mp hi0).resolve_left (by exact_mod_cast hρ.ne')
      exact ⟨π i, (hπ i).mpr (Finset.mem_filter.mpr ⟨hiS, hw0⟩), ht0⟩
    · rintro ⟨i', hi', ht0⟩
      have hmem : π.symm i' ∈ S.filter (fun i => w₀ i = 0) := (hπ (π.symm i')).mp (by simpa using hi')
      obtain ⟨hS', hw0⟩ := Finset.mem_filter.mp hmem
      refine ⟨π.symm i', hS', ?_⟩
      rw [hrec_i, hw0, Equiv.apply_symm_apply, ht0, mul_zero, zero_add]
  have hale : (S.filter fun i => w₀ i = 0).card ≤ n := by
    simpa using (S.filter fun i => w₀ i = 0).card_le_univ
  refine ⟨ρ, π, ⟨γ, (S.filter fun i => w₀ i = 0).card, hale,
    hanalytic, hmemP, himm, hinj, hbd⟩, hρ, hρhalf, hballW, fun t => rfl, ?_⟩
  intro i hi
  have hmem := (hπ (π.symm i)).mp (by simpa using hi)
  exact Finset.mem_filter.mp hmem

end PositivityTheory.Xgp.c_bm_exists_local
