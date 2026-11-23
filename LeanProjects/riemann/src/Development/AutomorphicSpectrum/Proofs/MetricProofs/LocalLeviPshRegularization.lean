import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalPshRegularizationLogBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalRegularizationGradientBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MollifyConvergesC2Rate
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section OneChart

variable {D : ℕ}

lemma oc_isClosed_coordDiv (S : Finset (Fin D)) : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
  have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
    ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
  rw [this]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const

lemma oc_q_bounds {q : (Fin D → ℂ) → ℝ} (hq : ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) 2)) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2), |q z| ≤ Q ∧ ‖fderiv ℝ q z‖ ≤ Q := by
  have hsub : closedBall (0 : Fin D → ℂ) (3 / 2) ⊆ ball 0 2 :=
    closedBall_subset_ball (by norm_num)
  have hc : IsCompact (closedBall (0 : Fin D → ℂ) (3 / 2)) := isCompact_closedBall _ _
  obtain ⟨a, ha⟩ := hc.exists_bound_of_continuousOn (hq.continuousOn.mono hsub)
  obtain ⟨b, hb⟩ := hc.exists_bound_of_continuousOn
    ((hq.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hsub)
  refine ⟨max (max a b) 0, le_max_right _ _, fun z hz => ?_⟩
  have hz' := ball_subset_closedBall hz
  have h1 : |q z| ≤ a := by simpa using ha z hz'
  exact ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hb z hz').trans ((le_max_right _ _).trans (le_max_left _ _))⟩

lemma fderiv_add_and_second_fderiv_add {W : Set (Fin D → ℂ)} (hW : IsOpen W) {q p : (Fin D → ℂ) → ℝ}
    (hq : ContDiffOn ℝ ∞ q W) (hp : ContDiffOn ℝ ∞ p W) {z : Fin D → ℂ} (hz : z ∈ W) :
    fderiv ℝ (fun x => q x + p x) z = fderiv ℝ q z + fderiv ℝ p z ∧
    fderiv ℝ (fderiv ℝ (fun x => q x + p x)) z =
      fderiv ℝ (fderiv ℝ q) z + fderiv ℝ (fderiv ℝ p) z := by
  have hd : ∀ {f : (Fin D → ℂ) → ℝ}, ContDiffOn ℝ ∞ f W → ∀ x ∈ W, DifferentiableAt ℝ f x :=
    fun hf x hx => (hf.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hx)
  have hd2 : ∀ f : (Fin D → ℂ) → ℝ, ContDiffOn ℝ ∞ f W →
      DifferentiableAt ℝ (fderiv ℝ f) z := fun f hf => by
    have h2 : ContDiffOn ℝ 2 f W := by exact_mod_cast contDiffOn_infty.1 hf 2
    exact ((h2.fderiv_of_isOpen (m := 1) hW one_add_one_eq_two.le).differentiableOn
      (by simp)).differentiableAt (hW.mem_nhds hz)
  have he : ∀ x ∈ W, fderiv ℝ (fun x => q x + p x) x = fderiv ℝ q x + fderiv ℝ p x :=
    fun x hx => fderiv_fun_add (hd hq x hx) (hd hp x hx)
  refine ⟨he z hz, ?_⟩
  have hev : fderiv ℝ (fun x => q x + p x) =ᶠ[𝓝 z] fun x => fderiv ℝ q x + fderiv ℝ p x :=
    Filter.eventually_of_mem (hW.mem_nhds hz) he
  rw [hev.fderiv_eq]
  exact fderiv_fun_add (hd2 q hq) (hd2 p hp)

lemma oc_tuo {E ι : Type*} [NormedAddCommGroup E] {l : Filter ι} {X : Type*} {K : Set X}
    {F G : ι → X → E} {f g : X → E} (h : TendstoUniformlyOn F f l K)
    (he : ∀ᶠ t in l, ∀ z ∈ K, G t z - g z = F t z - f z) : TendstoUniformlyOn G g l K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε, he] with t ht hte z hz
  have := ht z hz
  rw [dist_comm, dist_eq_norm] at this ⊢
  rw [hte z hz]
  exact this

lemma oc_ell {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

lemma oc_eps {t C₁ C : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) (hC₁ : 1 ≤ C₁)
    (hC : C₁ ≤ C) : epsT C₁ t ≤ epsT C t ∧ epsT C₁ t ≤ C₁ * Real.log (Real.log (1 / t)) := by
  obtain ⟨h1, h2⟩ := oc_ell ht hte
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hℓ : 0 < Real.log (1 / t) := by linarith
  unfold epsT
  constructor
  · apply div_le_div_of_nonneg_right _ hℓ.le
    exact mul_le_mul_of_nonneg_right hC (by linarith)
  · rw [div_le_iff₀ hℓ]
    have : 0 ≤ C₁ * Real.log (Real.log (1 / t)) := by positivity
    nlinarith

lemma oc_rLoc_ge (S : Finset (Fin D)) (m : Fin D → ℕ) {z : Fin D → ℂ}
    (hz : z ∈ ball (0 : Fin D → ℂ) (3 / 2)) :
    1 ≤ rLoc S m z ∧ 1 ≤ Real.log (rLoc S m z) := by
  have h := RegularChartScaling.rLoc_ge S m
    (RegularChartScaling.norm_coord_le_of_ball (R := 3 / 2) (by norm_num) hz)
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨he1.trans h, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at this

lemma oc_rLoc_cont (S : Finset (Fin D)) (m : Fin D → ℕ) :
    ContinuousOn (rLoc S m) (ReciprocityTheory.AnForm.A.coordDiv S)ᶜ := by
  unfold rLoc
  refine continuousOn_const.add (continuousOn_finset_sum _ fun i hi => ?_)
  refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
  · refine continuousOn_const.div (by fun_prop) ?_
    intro z hz
    have : z i ≠ 0 := fun h0 => hz ⟨i, hi, h0⟩
    positivity
  · intro z hz
    have : z i ≠ 0 := fun h0 => hz ⟨i, hi, h0⟩
    positivity

lemma oc_grad {r C₅ Q a b : ℝ} (hr : 1 ≤ r) (hC₅ : 0 ≤ C₅) (hQ : 0 ≤ Q) (ha : a ≤ Q)
    (hb : b ≤ C₅ * r ^ C₅ * Real.exp (r / 2)) :
    a + b ≤ (C₅ + Q) * r ^ (C₅ + Q) * Real.exp (r / 2) := by
  have h1 : r ^ C₅ ≤ r ^ (C₅ + Q) := Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have h2 : 1 ≤ r ^ (C₅ + Q) := Real.one_le_rpow hr (by linarith)
  have h3 : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  have h4 : 1 ≤ r ^ (C₅ + Q) * Real.exp (r / 2) := by nlinarith
  have h5 : C₅ * r ^ C₅ * Real.exp (r / 2) ≤ C₅ * (r ^ (C₅ + Q) * Real.exp (r / 2)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) hC₅
  nlinarith

end OneChart

theorem regularise_one_chart :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (q ph : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) (2)) → ContDiffOn ℝ ∞ ph (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) (fun z => q z + ph z) → (∀ z ∈ ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ ph z ∧ ph z ≤ C₅) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ ph z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ (C t₀ : ℝ) (phT : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ (∀ t, 0 < t → t ≤ t₀ → ContDiffOn ℝ ∞ (phT t) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (fun z => q z + phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ C ∧ -C * Real.log (Real.log (1 / t)) ≤ phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, ph z ≤ phT t z ∧ (rLoc S m z ≤ Real.log (1 / t) + K → phT t z ≤ ph z + t ^ ((1 : ℝ) / 3))) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), polyMaxOff S (fun x => q x + ph x) z t - epsT C t ≤ q z + phT t z ∧ q z + phT t z ≤ polyMaxOff S (fun x => q x + ph x) z t) ∧ ∀ t', t ≤ t' → t' ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ phT t' z + epsT C t') ∧ ∀ K' ⊆ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, IsCompact K' → TendstoUniformlyOn (fun t => phT t) (ph) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (phT t)) (fderiv ℝ (ph)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t))) (fderiv ℝ (fderiv ℝ (ph))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (phT t) z - fderiv ℝ (ph) z‖ ≤ M * t := by
  intro D S m q ph C₅ K hm hq hph hL hb hg
  have hAc := oc_isClosed_coordDiv S
  have hC₅ : 0 ≤ C₅ := RegularChartScaling.fifth_volume_constant_nonneg m le_rfl (by norm_num) hb
  obtain ⟨Q, hQ0, hQ⟩ := oc_q_bounds hq
  have hsub : ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S ⊆
      ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S :=
    Set.diff_subset_diff_left (ball_subset_ball (by norm_num))
  have hqA : ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    hq.mono Set.diff_subset
  have huS : ContDiffOn ℝ ∞ (fun z => q z + ph z)
      (ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S) := hqA.add hph
  have hO2 : IsOpen (ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hAc
  have hO3 : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hAc
  have hucont : ContinuousOn (fun z => q z + ph z)
      (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    huS.continuousOn.mono hsub
  have hupsh : ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S)
      (fun z => q z + ph z) :=
    (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ hO3 (hL.1.mono hsub)).2
      ⟨hL.1.mono hsub, fun z hz w => hL.2 z (hsub hz) w⟩
  have hubd : ∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S,
      -(C₅ + Q) * Real.log (rLoc S m z) ≤ q z + ph z ∧ q z + ph z ≤ C₅ + Q := by
    intro z hz
    obtain ⟨h1, h2⟩ := hb z (hsub hz)
    have h3 := abs_le.1 (hQ z hz.1).1
    have h4 := (oc_rLoc_ge S m hz.1).2
    constructor
    · nlinarith
    · linarith
  have hugrad : ∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S,
      ‖fderiv ℝ (fun z => q z + ph z) z‖ ≤
        (C₅ + Q) * rLoc S m z ^ (C₅ + Q) * Real.exp (rLoc S m z / 2) := by
    intro z hz
    rw [(fderiv_add_and_second_fderiv_add hO2 hqA hph (hsub hz)).1]
    exact (norm_add_le _ _).trans
      (oc_grad (oc_rLoc_ge S m hz.1).1 hC₅ hQ0 (hQ z hz.1).2 (hg z hz))
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨C₁, t₁, w, hC₁, ht₁, ht₁e, ht₁8, hW⟩ :=
    GlobalTheory.T.local_psh_regularization_log_bound D S m (fun z => q z + ph z) (C₅ + Q) ρ hucont hupsh hubd
  obtain ⟨t₂, ht₂, hN⟩ := GlobalTheory.T.local_regularization_gradient_bound D S m (fun z => q z + ph z) (C₅ + Q) K hm
    ((huS.differentiableOn (by simp)).mono hsub) hugrad
  obtain ⟨phT, hphT⟩ : ∃ phT : ℝ → (Fin D → ℂ) → ℝ,
      ∀ t z, phT t z = ReciprocityTheory.AnForm.A.molli ρ t (w t) z - q z := ⟨_, fun _ _ => rfl⟩
  have hphF : ∀ t, phT t = fun z => ReciprocityTheory.AnForm.A.molli ρ t (w t) z - q z :=
    fun t => funext (hphT t)
  have hgF : ∀ t, ReciprocityTheory.AnForm.A.molli ρ t (w t) = fun z => q z + phT t z := by
    intro t; funext z; rw [hphT]; ring
  have hq54 : ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), z ∈ ball (0 : Fin D → ℂ) (3 / 2) :=
    fun z hz => ball_subset_ball (by norm_num) hz
  have hqs : ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) (5 / 4)) :=
    hq.mono (ball_subset_ball (by norm_num))
  have hsmooth : ∀ t, 0 < t → t ≤ t₁ → ContDiffOn ℝ ∞ (phT t) (ball (0 : Fin D → ℂ) (5 / 4)) := by
    intro t ht htt
    rw [hphF]
    exact (hW t ht htt).2.1.sub hqs
  have hC1 : C₁ ≤ 2 * C₁ + 2 * Q + C₅ + 1 := by linarith
  refine ⟨2 * C₁ + 2 * Q + C₅ + 1, min t₁ t₂, phT, by linarith, lt_min ht₁ ht₂,
    (min_le_left _ _).trans ht₁e, fun t ht htt => ?_, fun K' hK' hcK' => ?_⟩
  · have ht1 : t ≤ t₁ := htt.trans (min_le_left _ _)
    have ht2 : t ≤ t₂ := htt.trans (min_le_right _ _)
    have hte := ht1.trans ht₁e
    obtain ⟨-, hs, hl, hge, hM⟩ := hW t ht ht1
    obtain ⟨hℓ1, hℓ2⟩ := oc_ell ht hte
    obtain ⟨he1, he2⟩ := oc_eps ht hte hC₁ hC1
    have hcb : ∀ s, s ≤ t₁ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), closedBall z s ⊆ ball 0 (3 / 2) :=
      fun s hs z hz => RegularChartScaling.closedBall_sub_of hz (by linarith)
    refine ⟨hsmooth t ht ht1, ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_,
      fun t' htt' ht' z hz => ?_⟩
    · rw [← hgF]; exact hl
    · obtain ⟨h1, h2, h3⟩ := hM z hz
      have hup : polyMaxOff S (fun z => q z + ph z) z t ≤ C₅ + Q :=
        RegularChartScaling.pmo_le z ht fun x hx => (hubd x ⟨hcb t ht1 z hz hx.1, hx.2⟩).2
      have hqz := abs_le.1 (hQ z (hq54 z hz)).1
      rw [hphT]
      constructor
      · linarith
      · nlinarith
    · obtain ⟨h1, h2, h3⟩ := hM z hz.1
      refine ⟨?_, fun hr => ?_⟩
      · rw [hphT]; have := hge z hz; linarith
      · rw [hphT]
        have h4 := hN t ht ht2 z hz hr
        have h5 : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
        linarith
    · obtain ⟨h1, h2, h3⟩ := hM z hz
      rw [hphT]
      constructor <;> linarith
    · have ht'0 : 0 < t' := ht.trans_le htt'
      have ht'1 : t' ≤ t₁ := ht'.trans (min_le_left _ _)
      have ht'e := ht'1.trans ht₁e
      obtain ⟨-, -, -, -, hM'⟩ := hW t' ht'0 ht'1
      obtain ⟨h1, h2, h3⟩ := hM z hz
      obtain ⟨h1', h2', h3'⟩ := hM' z hz
      obtain ⟨he1', -⟩ := oc_eps ht'0 ht'e hC₁ hC1
      have hmono : polyMaxOff S (fun z => q z + ph z) z t ≤
          polyMaxOff S (fun z => q z + ph z) z t' :=
        RegularChartScaling.pmo_mono (fun x hx => (hubd x hx).2) ht htt' (hcb t' ht'1 z hz)
      rw [hphT, hphT]
      linarith
  · have hK2 : K' ⊆ (ReciprocityTheory.AnForm.A.coordDiv S)ᶜ := fun z hz => (hK' hz).2
    obtain ⟨B, hB⟩ := (hcK'.image_of_continuousOn ((oc_rLoc_cont S m).mono hK2)).bddAbove
    obtain ⟨V, hVdef⟩ : ∃ V : Set (Fin D → ℂ),
        V = (ReciprocityTheory.AnForm.A.coordDiv S)ᶜ ∩ rLoc S m ⁻¹' Set.Iio (B + 1) ∩ ball 0 (5 / 4) :=
      ⟨_, rfl⟩
    have hV : IsOpen V := by
      rw [hVdef]
      exact ((oc_rLoc_cont S m).isOpen_inter_preimage hAc.isOpen_compl isOpen_Iio).inter isOpen_ball
    have hVsub : V ⊆ ball (0 : Fin D → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv S := by
      rw [hVdef]
      exact fun z hz => ⟨ball_subset_ball (by norm_num) hz.2, hz.1.1⟩
    have hKV : K' ⊆ V := by
      rw [hVdef]
      intro z hz
      have : rLoc S m z ≤ B := hB (Set.mem_image_of_mem _ hz)
      exact ⟨⟨hK2 hz, by simp only [Set.mem_preimage, Set.mem_Iio]; linarith⟩, (hK' hz).1⟩
    have hlog : Tendsto (fun t : ℝ => Real.log (Real.log (1 / t))) (𝓝[>] 0) atTop := by
      have h : Tendsto (fun t : ℝ => 1 / t) (𝓝[>] 0) atTop := by
        simpa only [one_div] using tendsto_inv_nhdsGT_zero
      exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h)
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min t₁ t₂ :=
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_min ht₁ ht₂))
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), Set.EqOn (w t) (fun z => q z + ph z) V := by
      filter_upwards [self_mem_nhdsWithin, hsmall,
        hlog.eventually_ge_atTop ((C₅ + Q) * Real.log (B + 1) / C₁)] with t ht htt hbig z hz
      have ht0 : 0 < t := ht
      have ht1 : t ≤ t₁ := htt.le.trans (min_le_left _ _)
      have hzV := hz
      rw [hVdef] at hz
      have hz3 := hq54 z hz.2
      have hzB : z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S :=
        ⟨hz3, hz.1.1⟩
      rw [(hW t ht0 ht1).1 z hzB]
      refine max_eq_left ?_
      have hr := oc_rLoc_ge S m hz3
      have hr2 : rLoc S m z < B + 1 := hz.1.2
      have hl : Real.log (rLoc S m z) ≤ Real.log (B + 1) :=
        Real.log_le_log (by linarith) hr2.le
      have h1 := (hubd z hzB).1
      have hC₁0 : 0 < C₁ := by linarith
      rw [div_le_iff₀ hC₁0] at hbig
      have hCQ : 0 ≤ C₅ + Q := by linarith
      nlinarith
    have huV : ContDiffOn ℝ ∞ (fun z => q z + ph z) V := huS.mono hVsub
    obtain ⟨h1, h2, h3, M, h4⟩ := mollify_converges_C2_rate D ρ V K' (fun z => q z + ph z)
      (fun t => w t) hV hcK' hKV huV hev
    have hO : IsOpen (ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
      isOpen_ball.sdiff hAc
    have hOsub : ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S ⊆
        ball 0 2 \ ReciprocityTheory.AnForm.A.coordDiv S :=
      Set.diff_subset_diff_left (ball_subset_ball (by norm_num))
    have hd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        fderiv ℝ (phT t) z - fderiv ℝ ph z =
          fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ (fun z => q z + ph z) z ∧
        fderiv ℝ (fderiv ℝ (phT t)) z - fderiv ℝ (fderiv ℝ ph) z =
          fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) z -
            fderiv ℝ (fderiv ℝ (fun z => q z + ph z)) z := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htt z hz
      have ht0 : 0 < t := ht
      have hs := hsmooth t ht0 (htt.le.trans (min_le_left _ _))
      have hzO := hK' hz
      obtain ⟨a1, a2⟩ := fderiv_add_and_second_fderiv_add hO (hqs.mono Set.diff_subset) (hs.mono Set.diff_subset) hzO
      obtain ⟨b1, b2⟩ := fderiv_add_and_second_fderiv_add hO (hqs.mono Set.diff_subset) (hph.mono hOsub) hzO
      rw [hgF t, a1, a2, b1, b2]
      constructor <;> abel
    refine ⟨oc_tuo h1 ?_, oc_tuo h2 (hd.mono fun t ht z hz => (ht z hz).1),
      oc_tuo h3 (hd.mono fun t ht z hz => (ht z hz).2), M, ?_⟩
    · refine Filter.Eventually.of_forall fun t z _ => ?_
      rw [hphT]; ring
    · filter_upwards [h4, hd] with t ht htd z hz
      rw [(htd z hz).1]
      exact ht z hz

end GlobalTheory.CompanionTheory.Ar.Giv
