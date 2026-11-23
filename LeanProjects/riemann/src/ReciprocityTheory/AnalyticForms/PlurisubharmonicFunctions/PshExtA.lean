import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson

open Metric Real Filter Topology MeasureTheory

namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

section
theorem cA_mul (b : ℝ) (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    circleAverage (fun z => b * f z) c R = b * circleAverage f c R := by
  simp only [circleAverage, smul_eq_mul, intervalIntegral.integral_const_mul]; ring

theorem mp_core {k : ℂ → ℝ} {c ζ0 : ℂ} {r η : ℝ} {E : Finset ℂ}
    (hζ0 : ζ0 ∈ closedBall c r) (hζ0E : ζ0 ∉ E) (hη : 0 < η)
    (hcont : ContinuousOn k (closedBall c r \ ↑E))
    (hsph : ∀ ζ ∈ sphere c r, k ζ < k ζ0)
    (hpunct : ∀ e ∈ E, ∀ ζ ∈ closedBall c r \ ↑E, 0 < dist ζ e → dist ζ e < η → k ζ < k ζ0)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball c r \ ↑E → k a < circleAverage k a s) :
    False := by
  set K := closedBall c r \ ⋃ e ∈ E, ball e (η / 2) with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall c r).diff (isOpen_biUnion fun e _ => isOpen_ball)
  have hKE : K ⊆ closedBall c r \ ↑E := by
    intro x hx
    refine ⟨hx.1, fun hxE => hx.2 ?_⟩
    exact Set.mem_biUnion hxE (mem_ball_self (by linarith))
  have hζ0K : ζ0 ∈ K := by
    refine ⟨hζ0, ?_⟩
    simp only [Set.mem_iUnion, mem_ball, not_exists]
    intro e he hd
    have hpos : 0 < dist ζ0 e := dist_pos.2 (fun h => hζ0E (h ▸ he))
    exact lt_irrefl _ (hpunct e he ζ0 ⟨hζ0, hζ0E⟩ hpos (by linarith))
  obtain ⟨ζ1, hζ1K, hmax⟩ := hKc.exists_isMaxOn ⟨ζ0, hζ0K⟩ (hcont.mono hKE)
  have h10 : k ζ0 ≤ k ζ1 := hmax hζ0K
  have hin : dist ζ1 c < r := by
    rcases (mem_closedBall.1 hζ1K.1).lt_or_eq with h | h
    · exact h
    · exact absurd (hsph ζ1 (mem_sphere.2 h)) (not_lt.2 h10)
  have hfar : ∀ e ∈ E, η ≤ dist ζ1 e := by
    intro e he
    by_contra hlt
    push Not at hlt
    have h2 : η / 2 ≤ dist ζ1 e := by
      by_contra h3
      push Not at h3
      exact hζ1K.2 (Set.mem_biUnion he (mem_ball.2 h3))
    exact absurd (hpunct e he ζ1 (hKE hζ1K) (by linarith) hlt) (not_lt.2 h10)
  set s := min (r - dist ζ1 c) (η / 2) / 2 with hs
  have hm0 : 0 < min (r - dist ζ1 c) (η / 2) := lt_min (by linarith) (by linarith)
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s ≤ (r - dist ζ1 c) / 2 := by
    have := min_le_left (r - dist ζ1 c) (η / 2); rw [hs]; linarith
  have hs2 : s ≤ η / 4 := by
    have := min_le_right (r - dist ζ1 c) (η / 2); rw [hs]; linarith
  have hsK : closedBall ζ1 s ⊆ K := by
    intro x hx
    have hx' := mem_closedBall.1 hx
    refine ⟨mem_closedBall.2 ?_, ?_⟩
    · linarith [dist_triangle x ζ1 c]
    · simp only [Set.mem_iUnion, mem_ball, not_exists, not_lt]
      intro e he
      have h1 := hfar e he
      have h2 := dist_triangle ζ1 x e
      rw [dist_comm ζ1 x] at h2
      linarith
  have hsB : closedBall ζ1 s ⊆ ball c r \ ↑E := by
    intro x hx
    refine ⟨mem_ball.2 ?_, (hKE (hsK hx)).2⟩
    have hx' := mem_closedBall.1 hx
    linarith [dist_triangle x ζ1 c]
  have hlt := hsub ζ1 s hs0 hsB
  have hle : circleAverage k ζ1 s ≤ k ζ1 := by
    apply circleAverage_mono_on_of_le_circle
    · apply ContinuousOn.circleIntegrable hs0.le
      exact (hcont.mono hKE).mono (sphere_subset_closedBall.trans hsK)
    · intro x hx
      rw [abs_of_pos hs0] at hx
      exact hmax (hsK (sphere_subset_closedBall hx))
  linarith

theorem circleAverage_norm_sub_sq (a c : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    circleAverage (fun ζ => ‖ζ - c‖ ^ 2) a s = ‖a - c‖ ^ 2 + s ^ 2 := by
  have hpt : ∀ ζ ∈ sphere a |s|, ‖ζ - c‖ ^ 2 =
      (‖a - c‖ ^ 2 + s ^ 2) + 2 * ((starRingEnd ℂ (a - c)) * (ζ - a)).re := by
    intro ζ hζ
    rw [abs_of_nonneg hs, mem_sphere, dist_eq_norm] at hζ
    have : ζ - c = (a - c) + (ζ - a) := by ring
    rw [this, ← hζ, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp [Complex.mul_re]
    ring
  rw [circleAverage_congr_sphere hpt]
  have hh : circleAverage (fun ζ => (starRingEnd ℂ (a - c)) * (ζ - a)) a s = 0 := by
    rw [circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty]
    · simp
    · exact (by fun_prop : Continuous fun ζ : ℂ => (starRingEnd ℂ (a - c)) * (ζ - a)).continuousOn
    · intro z _; fun_prop
  have hre : circleAverage (fun ζ => ((starRingEnd ℂ (a - c)) * (ζ - a)).re) a s = 0 := by
    have h2 : CircleIntegrable (fun ζ => (starRingEnd ℂ (a - c)) * (ζ - a)) a s :=
      (by fun_prop : Continuous fun ζ : ℂ => (starRingEnd ℂ (a - c)) * (ζ - a)).continuousOn.circleIntegrable'
    have := Complex.reCLM.circleAverage_comp_comm h2
    simp only [Function.comp_def, Complex.reCLM_apply] at this
    rw [this, hh]; simp
  have h2 : circleAverage (fun x => 2 * ((starRingEnd ℂ) (a - c) * (x - a)).re) a s =
      2 * circleAverage (fun x => ((starRingEnd ℂ) (a - c) * (x - a)).re) a s :=
    cA_mul _ _ _ _
  rw [circleAverage_fun_add, circleAverage_const, h2, hre]
  · simp
  · exact (continuous_const).continuousOn.circleIntegrable'
  · exact (by fun_prop : Continuous fun ζ : ℂ => 2 * ((starRingEnd ℂ (a - c)) * (ζ - a)).re).continuousOn.circleIntegrable'

noncomputable def pert (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) (ζ : ℂ) : ℝ :=
  ε * ∑ f ∈ E, log ‖ζ - f‖ + δ * ‖ζ - c‖ ^ 2

theorem pert_continuousOn (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) :
    ContinuousOn (pert E c ε δ) (↑E)ᶜ := by
  have hlog : ∀ f ∈ E, ContinuousOn (fun ζ : ℂ => log ‖ζ - f‖) (↑E)ᶜ := by
    intro f hf
    apply ContinuousOn.log (by fun_prop)
    intro x hx hx0
    rw [norm_eq_zero, sub_eq_zero] at hx0
    exact hx (hx0 ▸ hf)
  unfold pert
  exact (continuousOn_const.mul (continuousOn_finsetSum E hlog)).add (by fun_prop)

theorem pert_submean {E : Finset ℂ} {c a : ℂ} {s ε δ : ℝ} (hs : 0 < s) (hε : 0 ≤ ε)
    (haE : a ∉ E) (hE : ∀ f ∈ E, f ∉ sphere a s) :
    CircleIntegrable (pert E c ε δ) a s ∧
      pert E c ε δ a + δ * s ^ 2 ≤ circleAverage (pert E c ε δ) a s := by
  have hlogc : ∀ f ∈ E, ContinuousOn (fun ζ : ℂ => log ‖ζ - f‖) (sphere a |s|) := by
    intro f hf
    apply ContinuousOn.log (by fun_prop)
    intro x hx hx0
    rw [norm_eq_zero, sub_eq_zero] at hx0
    rw [abs_of_pos hs] at hx
    exact hE f hf (hx0 ▸ hx)
  have hli : ∀ f ∈ E, CircleIntegrable (fun ζ : ℂ => log ‖ζ - f‖) a s :=
    fun f hf => (hlogc f hf).circleIntegrable'
  have hsumc : ContinuousOn (fun ζ : ℂ => ∑ f ∈ E, log ‖ζ - f‖) (sphere a |s|) :=
    continuousOn_finsetSum E hlogc
  have hqi : CircleIntegrable (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s :=
    (by fun_prop : Continuous fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2).continuousOn.circleIntegrable'
  have hsi : CircleIntegrable (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s :=
    (continuousOn_const.mul hsumc).circleIntegrable'
  refine ⟨hsi.add hqi, ?_⟩
  unfold pert
  rw [circleAverage_fun_add hsi hqi]
  have h1 : circleAverage (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s
      = ε * ∑ f ∈ E, circleAverage (fun ζ : ℂ => log ‖ζ - f‖) a s := by
    rw [show circleAverage (fun ζ : ℂ => ε * ∑ f ∈ E, log ‖ζ - f‖) a s
      = ε * circleAverage (fun ζ : ℂ => ∑ f ∈ E, log ‖ζ - f‖) a s from cA_mul _ _ _ _]
    rw [circleAverage_fun_sum hli]
  have h2 : circleAverage (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s = δ * (‖a - c‖ ^ 2 + s ^ 2) := by
    rw [show circleAverage (fun ζ : ℂ => δ * ‖ζ - c‖ ^ 2) a s
      = δ * circleAverage (fun ζ : ℂ => ‖ζ - c‖ ^ 2) a s from cA_mul _ _ _ _]
    rw [circleAverage_norm_sub_sq a c hs.le]
  rw [h1, h2]
  have h3 : ∑ f ∈ E, log ‖a - f‖ ≤ ∑ f ∈ E, circleAverage (fun ζ : ℂ => log ‖ζ - f‖) a s := by
    apply Finset.sum_le_sum
    intro f hf
    have haf : a - f ≠ 0 := sub_ne_zero.2 (fun h => haE (h ▸ hf))
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hs.ne']
    have : log ‖a - f‖ = log s + log (s⁻¹ * ‖a - f‖) := by
      rw [log_mul (inv_ne_zero hs.ne') (norm_ne_zero_iff.2 haf), log_inv]; ring
    rw [this]
    have : log (s⁻¹ * ‖a - f‖) ≤ log⁺ (s⁻¹ * ‖a - f‖) := le_max_right _ _
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hε
  nlinarith

end

section

theorem smg2 {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hgrow : ∀ ε > 0, ∀ T : ℝ, ∃ η > 0, ∀ e ∈ F, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F,
      dist ζ e < η → g ζ + ε * log ‖ζ - e‖ < T)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by
  have hsph : sphere (0 : ℂ) r ⊆ closedBall 0 r \ ↑F := fun x hx =>
    ⟨sphere_subset_closedBall hx, fun hxF => by
      have h1 := hFr x hxF
      rw [mem_ball] at h1
      rw [mem_sphere] at hx
      linarith⟩
  obtain ⟨Φ, hΦc, hΦs, hΦ0, hΦm⟩ := poisson_ext hr (hc.mono hsph)
  by_contra hlt
  push Not at hlt
  set γ := g 0 - Φ 0 with hγ
  have hγ0 : 0 < γ := by rw [hγ, hΦ0]; linarith
  obtain ⟨BΦ, hBΦ⟩ : ∃ BΦ, ∀ ζ ∈ closedBall (0 : ℂ) r, -Φ ζ ≤ BΦ := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).bddAbove_image hΦc.neg
    exact ⟨M, fun ζ hζ => hM ⟨ζ, hζ, rfl⟩⟩
  set L := (F.card : ℝ) * log (2 * r) - ∑ f ∈ F, log ‖(0 : ℂ) - f‖ with hL
  set ε := γ / (4 * (|L| + 1)) with hε
  set δ := γ / (4 * (r ^ 2 + 1)) with hδ
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 < δ := by positivity
  have hεL : ε * L < γ / 4 := by
    have : ε * (|L| + 1) = γ / 4 := by rw [hε]; field_simp
    nlinarith [le_abs_self L]
  have hδr : δ * r ^ 2 < γ / 4 := by
    have : δ * (r ^ 2 + 1) = γ / 4 := by rw [hδ]; field_simp
    nlinarith
  set k : ℂ → ℝ := fun ζ => (g ζ - Φ ζ) + pert F 0 ε δ ζ with hk
  have hk0 : k 0 = γ + ε * ∑ f ∈ F, log ‖(0 : ℂ) - f‖ := by
    simp [hk, pert, hγ]
  have hlog2r : ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, ∀ f ∈ F, log ‖ζ - f‖ ≤ log (2 * r) := by
    intro ζ hζ f hf
    have hne : ζ - f ≠ 0 := sub_ne_zero.2 (fun h => hζ.2 (h ▸ hf))
    apply log_le_log (norm_pos_iff.2 hne)
    have h1 := mem_closedBall_zero_iff.1 hζ.1
    have h2 := mem_ball_zero_iff.1 (hFr f hf)
    calc ‖ζ - f‖ ≤ ‖ζ‖ + ‖f‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have hsumle : ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F,
      ∑ f ∈ F, log ‖ζ - f‖ ≤ (F.card : ℝ) * log (2 * r) := by
    intro ζ hζ
    have := Finset.sum_le_sum (fun f hf => hlog2r ζ hζ f hf)
    simpa using this
  obtain ⟨η, hη, hηp⟩ := hgrow ε hε0
    (k 0 - BΦ - δ * r ^ 2 - ε * ((F.card : ℝ) * |log (2 * r)|))
  apply mp_core (k := k) (c := 0) (ζ0 := 0) (r := r) (E := F) (η := η)
    (by simp [hr.le]) hF0 hη
  ·
    refine ((hc.sub (hΦc.mono Set.sdiff_subset))).add ((pert_continuousOn F 0 ε δ).mono ?_)
    intro x hx; exact hx.2
  ·
    intro ζ hζ
    have hζ' := hsph hζ
    have h1 : g ζ - Φ ζ = 0 := by rw [hΦs ζ hζ]; ring
    have h2 : ‖ζ - 0‖ ^ 2 = r ^ 2 := by
      rw [sub_zero, mem_sphere_zero_iff_norm.1 hζ]
    have h00 : δ * ‖(0 : ℂ) - 0‖ ^ 2 = 0 := by simp
    simp only [hk, pert, h1, h2]
    have := hsumle ζ hζ'
    have h3 := mul_le_mul_of_nonneg_left this hε0.le
    have : ε * L = ε * ((F.card : ℝ) * log (2 * r)) - ε * ∑ f ∈ F, log ‖(0 : ℂ) - f‖ := by
      rw [hL]; ring
    linarith
  ·
    intro e he ζ hζ _ hd
    have hgp := hηp e he ζ hζ hd
    have hsplit : ∑ f ∈ F, log ‖ζ - f‖ = log ‖ζ - e‖ + ∑ f ∈ F.erase e, log ‖ζ - f‖ :=
      (Finset.add_sum_erase F _ he).symm
    have herase : ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ (F.card : ℝ) * |log (2 * r)| := by
      calc ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ ∑ f ∈ F.erase e, |log (2 * r)| :=
            Finset.sum_le_sum (fun f hf =>
              (hlog2r ζ hζ f (Finset.mem_of_mem_erase hf)).trans (le_abs_self _))
        _ = ((F.erase e).card : ℝ) * |log (2 * r)| := by simp
        _ ≤ (F.card : ℝ) * |log (2 * r)| := by
            gcongr
            exact Finset.erase_subset e F
    have hq : ‖ζ - 0‖ ^ 2 ≤ r ^ 2 := by
      rw [sub_zero]
      have := mem_closedBall_zero_iff.1 hζ.1
      gcongr
    have hP := hBΦ ζ hζ.1
    have hk' : k ζ = g ζ - Φ ζ + (ε * ∑ f ∈ F, log ‖ζ - f‖ + δ * ‖ζ - 0‖ ^ 2) := rfl
    rw [hk', hsplit]
    have : δ * ‖ζ - 0‖ ^ 2 ≤ δ * r ^ 2 := mul_le_mul_of_nonneg_left hq hδ0.le
    have : ε * ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ ε * ((F.card : ℝ) * |log (2 * r)|) :=
      mul_le_mul_of_nonneg_left herase hε0.le
    nlinarith
  ·
    intro a s hs hsub'
    have haF : a ∉ F := (hsub' (mem_closedBall_self hs.le)).2
    have hFs : ∀ f ∈ F, f ∉ sphere a s := fun f hf hfs =>
      (hsub' (sphere_subset_closedBall hfs)).2 hf
    obtain ⟨hpi, hpm⟩ := pert_submean (c := 0) (δ := δ) hs hε0.le haF hFs
    have hsB : sphere a |s| ⊆ closedBall (0 : ℂ) r \ ↑F := by
      rw [abs_of_pos hs]
      intro x hx
      have := hsub' (sphere_subset_closedBall hx)
      exact ⟨ball_subset_closedBall this.1, this.2⟩
    have hgi : CircleIntegrable g a s := (hc.mono hsB).circleIntegrable'
    have hΦi : CircleIntegrable Φ a s := (hΦc.mono (hsB.trans Set.sdiff_subset)).circleIntegrable'
    have hav : circleAverage k a s =
        circleAverage g a s - circleAverage Φ a s + circleAverage (pert F 0 ε δ) a s := by
      have e1 := circleAverage_fun_add (hgi.sub hΦi) hpi
      have e2 : circleAverage (g - Φ) a s = circleAverage g a s - circleAverage Φ a s :=
        circleAverage_fun_sub hgi hΦi
      simp only [Pi.sub_apply] at e1
      rw [hk, e1, e2]
    have hΦa : circleAverage Φ a s = Φ a :=
      hΦm a s hs (fun x hx => (hsub' hx).1)
    have hga := hsub a s hs hsub'
    rw [hav, hΦa]
    have : 0 < δ * s ^ 2 := by positivity
    simp only [hk]
    linarith

theorem smg {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hB : ∃ B, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, g ζ ≤ B)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by
  obtain ⟨B, hB⟩ := hB
  refine smg2 hr hF0 hFr hc ?_ hsub
  intro ε hε T
  refine ⟨exp ((T - B) / ε), exp_pos _, ?_⟩
  intro e he ζ hζ hd
  have hne : ζ - e ≠ 0 := sub_ne_zero.2 (fun h => hζ.2 (h ▸ he))
  have hlog : log ‖ζ - e‖ < (T - B) / ε := by
    rw [dist_eq_norm] at hd
    exact (log_lt_iff_lt_exp (norm_pos_iff.2 hne)).2 hd
  have : ε * log ‖ζ - e‖ < T - B := by
    have := mul_lt_mul_of_pos_left hlog hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  linarith [hB ζ hζ]

theorem exists_sphere_ge {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g (sphere 0 r)) (h : g 0 ≤ circleAverage g 0 r) :
    ∃ ζ ∈ sphere (0 : ℂ) r, g 0 ≤ g ζ := by
  by_contra hno
  push Not at hno
  obtain ⟨ζ1, hζ1, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr.le) hc
  have hle : circleAverage g 0 r ≤ g ζ1 := by
    apply circleAverage_mono_on_of_le_circle
    · exact hc.circleIntegrable hr.le
    · intro x hx
      rw [abs_of_pos hr] at hx
      exact hmax hx
  linarith [hno ζ1 hζ1]

end

end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
