import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvd

open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section
namespace GlobalTheory.RootHs
open Metric Complex

lemma mem_ball_big (u : ℂ) (R ε : ℝ) (hε : 0 < ε) (hu : 2 * ε ≤ u.im) (hR : u.re ^ 2 + u.im ^ 2 < R * u.im)
    (hRε : ε < R) : u ∈ ball ((R : ℂ) * I) (R - ε) := by
  have hRe : 0 ≤ R - ε := by linarith
  rw [Metric.mem_ball, Complex.dist_eq]
  have hsq : ‖u - (R : ℂ) * I‖ ^ 2 = u.re ^ 2 + (u.im - R) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hlt : ‖u - (R : ℂ) * I‖ ^ 2 < (R - ε) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R) (by linarith : (0:ℝ) ≤ u.im - 2 * ε), sq_nonneg ε]
  nlinarith [norm_nonneg (u - (R : ℂ) * I)]

lemma closedBall_big_sub (R ε : ℝ) (hε : 0 < ε) : closedBall ((R : ℂ) * I) (R - ε) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h1 := Complex.abs_im_le_norm (z - (R : ℂ) * I)
  have h2 : (z - (R : ℂ) * I).im = z.im - R := by simp
  rw [h2] at h1
  show 0 < z.im
  have h3 := neg_abs_le (z.im - R)
  linarith

lemma exists_disc (z₀ z : ℂ) (h₀ : 0 < z₀.im) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), closedBall c r ⊆ Hs ∧ z₀ ∈ ball c r ∧ z ∈ ball c r := by
  set ε : ℝ := min z₀.im z.im / 2 with hεdef
  have hε : 0 < ε := half_pos (lt_min h₀ hz)
  have h2ε₀ : 2 * ε ≤ z₀.im := by rw [hεdef]; linarith [min_le_left z₀.im z.im]
  have h2ε : 2 * ε ≤ z.im := by rw [hεdef]; linarith [min_le_right z₀.im z.im]
  have ha : 0 ≤ (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im := div_nonneg (by positivity) h₀.le
  have hb : 0 ≤ (z.re ^ 2 + z.im ^ 2) / z.im := div_nonneg (by positivity) hz.le
  set R : ℝ := (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im + (z.re ^ 2 + z.im ^ 2) / z.im + ε + 1 with hRdef
  have hR₀ : z₀.re ^ 2 + z₀.im ^ 2 < R * z₀.im := (div_lt_iff₀ h₀).mp (by rw [hRdef]; linarith)
  have hR : z.re ^ 2 + z.im ^ 2 < R * z.im := (div_lt_iff₀ hz).mp (by rw [hRdef]; linarith)
  have hRε : ε < R := by rw [hRdef]; linarith
  exact ⟨(R : ℂ) * I, R - ε, closedBall_big_sub R ε hε, mem_ball_big z₀ R ε hε h2ε₀ hR₀ hRε,
    mem_ball_big z R ε hε h2ε hR hRε⟩

theorem discRoot : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    (∃ z₀ ∈ Hs, h z₀ ≠ 0) → ∀ (c : ℂ) (r : ℝ), Metric.closedBall c r ⊆ Hs →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball c r) ∧ ∀ z ∈ Metric.ball c r, g z ^ m = h z := by
  rintro h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz => ?_⟩
    rw [Metric.ball_eq_empty.mpr hr] at hz
    exact absurd hz (Set.notMem_empty z)
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have hHsConn : IsPreconnected Hs := by
    show IsPreconnected {z : ℂ | 0 < z.im}
    exact (convex_halfSpace_im_gt (r := 0)).isPreconnected
  have han : AnalyticOnNhd ℂ h Hs := hh.analyticOnNhd hHsOpen
  refine GlobalTheory.KZ.RootDisc.exists_root_disc h m c r hm hr (han.mono hsub) ?_
  intro τ hτ
  have hτ' := hsub hτ
  have hfin : analyticOrderAt h τ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hne (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHsConn hτ' htop hz₀)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hmer : meromorphicOrderAt h τ = ((n : ℤ) : WithTop ℤ) := by
    rw [(han τ hτ').meromorphicOrderAt_eq, ← hn]
    rfl
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.mp (hdiv τ hτ' n hmer)
  exact ⟨k, by rw [← hn, hk]⟩

theorem rootUnique : ∀ (U : Set ℂ) (g₁ g₂ : ℂ → ℂ) (m : ℕ) (z₀ : ℂ), 0 < m → IsOpen U → IsPreconnected U →
    DifferentiableOn ℂ g₁ U → DifferentiableOn ℂ g₂ U → (∀ z ∈ U, g₁ z ^ m = g₂ z ^ m) → z₀ ∈ U →
    g₁ z₀ = g₂ z₀ → g₁ z₀ ≠ 0 → Set.EqOn g₁ g₂ U := by
  intro U g₁ g₂ m z₀ hm hU hC hg₁ hg₂ hpow hz₀ heq hne
  have hc₁ : ContinuousAt g₁ z₀ := (hg₁.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hc₂ : ContinuousAt g₂ z₀ := (hg₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hq : ContinuousAt (fun z => g₂ z / g₁ z) z₀ := hc₂.div hc₁ hne
  have hq0 : g₂ z₀ / g₁ z₀ = 1 := by rw [← heq, div_self hne]
  set S : Finset ℂ := (Polynomial.nthRoots m (1 : ℂ)).toFinset.erase 1 with hSdef
  have hS : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
  have hopen : (S : Set ℂ)ᶜ ∈ 𝓝 (g₂ z₀ / g₁ z₀) := by
    rw [hq0]
    exact hS.isOpen_compl.mem_nhds (by simp [hSdef])
  have hev : g₁ =ᶠ[𝓝 z₀] g₂ := by
    filter_upwards [hq.preimage_mem_nhds hopen, hc₁.eventually_ne hne, hU.mem_nhds hz₀] with z hzS hz1 hzU
    have hroot : g₂ z / g₁ z ∈ Polynomial.nthRoots m (1 : ℂ) := by
      rw [Polynomial.mem_nthRoots hm, div_pow, ← hpow z hzU, div_self (pow_ne_zero _ hz1)]
    have h1 : g₂ z / g₁ z = 1 := by
      by_contra hne1
      exact hzS (Finset.mem_erase.mpr ⟨hne1, Multiset.mem_toFinset.mpr hroot⟩)
    rw [div_eq_one_iff_eq hz1] at h1
    exact h1.symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hg₁.analyticOnNhd hU) (hg₂.analyticOnNhd hU) hC hz₀ hev

theorem rootHs : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  classical
  intro h m hm hh hdiv
  by_cases hz : ∃ z₀ ∈ Hs, h z₀ ≠ 0
  swap
  · simp only [not_exists, not_and, not_not] at hz
    refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz' => ?_⟩
    rw [hz z hz', zero_pow hm.ne']
  obtain ⟨z₀, hz₀, hne⟩ := hz
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hm
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hw₀, zero_pow hm.ne'])
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have key : ∀ z ∈ Hs, ∃ (c : ℂ) (r : ℝ), z₀ ∈ ball c r ∧ z ∈ ball c r ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball c r) ∧ (∀ y ∈ ball c r, g y ^ m = h y) ∧ g z₀ = w₀ := by
    intro z hz
    obtain ⟨c, r, hsub, h0, h1⟩ := exists_disc z₀ z hz₀ hz
    obtain ⟨g, hgd, hgp⟩ := discRoot h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
    have hg0 : g z₀ ≠ 0 := by
      intro h0'
      apply hne
      rw [← hgp z₀ h0, h0', zero_pow hm.ne']
    refine ⟨c, r, h0, h1, fun y => (w₀ / g z₀) * g y, hgd.const_mul _, fun y hy => ?_, ?_⟩
    · rw [mul_pow, div_pow, hgp y hy, hw₀, hgp z₀ h0, div_self hne, one_mul]
    · exact div_mul_cancel₀ w₀ hg0
  choose c r h0 h1 g hgd hgp hgz using key
  have hloc : ∀ z₁ (hz₁ : z₁ ∈ Hs) z (hz : z ∈ Hs), z ∈ ball (c z₁ hz₁) (r z₁ hz₁) →
      g z hz z = g z₁ hz₁ z := by
    intro z₁ hz₁ z hz hzb
    have hU : IsOpen (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) := isOpen_ball.inter isOpen_ball
    have hC : IsPreconnected (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    refine rootUnique _ (g z hz) (g z₁ hz₁) m z₀ hm hU hC ((hgd z hz).mono Set.inter_subset_left)
      ((hgd z₁ hz₁).mono Set.inter_subset_right) (fun y hy => by rw [hgp z hz y hy.1, hgp z₁ hz₁ y hy.2])
      ⟨h0 z hz, h0 z₁ hz₁⟩ ((hgz z hz).trans (hgz z₁ hz₁).symm) (by rw [hgz z hz]; exact hw₀ne) ⟨h1 z hz, hzb⟩
  refine ⟨fun z => if h' : z ∈ Hs then g z h' z else 0, ?_, ?_⟩
  · intro z₁ hz₁
    have hev : (fun z => if h' : z ∈ Hs then g z h' z else 0) =ᶠ[𝓝 z₁] g z₁ hz₁ := by
      have hmem : ball (c z₁ hz₁) (r z₁ hz₁) ∩ Hs ∈ 𝓝 z₁ := (isOpen_ball.inter hHsOpen).mem_nhds ⟨h1 z₁ hz₁, hz₁⟩
      filter_upwards [hmem] with z hz
      show (if h' : z ∈ Hs then g z h' z else 0) = g z₁ hz₁ z
      rw [dif_pos hz.2]
      exact hloc z₁ hz₁ z hz.2 hz.1
    exact (((hgd z₁ hz₁).differentiableAt (isOpen_ball.mem_nhds (h1 z₁ hz₁))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    show (if h' : z ∈ Hs then g z h' z else 0) ^ m = h z
    rw [dif_pos hz]
    exact hgp z hz z (h1 z hz)

end GlobalTheory.RootHs
