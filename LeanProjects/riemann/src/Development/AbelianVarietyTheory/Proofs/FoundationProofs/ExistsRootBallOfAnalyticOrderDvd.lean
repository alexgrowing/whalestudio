import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section
namespace GlobalTheory.KZ.RootDisc

open Metric Filter Topology

theorem exists_root_of_ne_zero (g : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ) (hm : 0 < m)
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0) (hR : 0 < R) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball c R) ∧ ∀ z ∈ ball c R, s z ^ m = g z := by
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨L, hL0, hL⟩ := hd.isExactOn_ball.with_val_at c (Complex.log (g c))
  have hc : c ∈ ball c R := mem_ball_self hR
  have hgd : ∀ z ∈ ball c R, HasDerivAt g (deriv g z) z := fun z hz =>
    ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hh : ∀ z ∈ ball c R, HasDerivAt (fun w => g w * Complex.exp (-L w)) 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w => g w * Complex.exp (-L w))
        (deriv g z * Complex.exp (-L z) + g z * (Complex.exp (-L z) * -(deriv g z / g z))) z :=
      (hgd z hz).mul ((hL z hz).neg.cexp)
    refine h1.congr_deriv ?_
    have e : g z * (deriv g z / g z) = deriv g z := mul_div_cancel₀ _ (hne z hz)
    linear_combination (-Complex.exp (-L z)) * e
  have hexp : ∀ z ∈ ball c R, g z = Complex.exp (L z) := by
    intro z hz
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hh z hz).deriv) hz hc
    simp only [hL0, Complex.exp_neg, Complex.exp_log (hne c hc)] at hconst
    rw [mul_inv_cancel₀ (hne c hc)] at hconst
    have := Complex.exp_ne_zero (L z)
    field_simp at hconst
    exact hconst
  refine ⟨fun z => Complex.exp (L z / m), ?_, ?_⟩
  · intro z hz
    exact (((hL z hz).differentiableAt.div_const (m : ℂ)).cexp).differentiableWithinAt
  · intro z hz
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hm', hexp z hz]

end GlobalTheory.KZ.RootDisc

namespace GlobalTheory.KZ.RootDisc
open Metric Filter Topology

theorem exists_root_disc : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R →
    AnalyticOnNhd ℂ h (Metric.closedBall c R) →
    (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  intro h m c R hm hR hh hord
  set U := closedBall c R with hU
  have hmer : MeromorphicOn h U := hh.meromorphicOn
  have htop : ∀ u : U, meromorphicOrderAt h u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := hord u hu
    rw [(hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe]
    exact WithTop.coe_ne_top
  have hfin : (MeromorphicOn.divisor h U).support.Finite := (MeromorphicOn.divisor h U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg, hgne, hgeq⟩ := hmer.extract_zeros_poles htop hfin
  set d := MeromorphicOn.divisor h U with hd
  set S := hfin.toFinset with hS
  have hdU : ∀ u ∈ U, ∃ k : ℕ, d u = ((m * k : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hord u hu
    refine ⟨k, ?_⟩
    rw [hd, MeromorphicOn.divisor_apply hmer hu, (hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe, WithTop.untop₀_coe]
  let kk : ℂ → ℕ := fun u => (d u).toNat / m
  have hkk : ∀ u ∈ U, d u = ((m * kk u : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hdU u hu
    have : kk u = k := by
      simp only [kk, hk, Int.toNat_natCast]
      exact Nat.mul_div_cancel_left k hm
    rw [this, hk]
  have hSU : ∀ u ∈ S, u ∈ U := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    exact d.supportWithinDomain hu
  let q : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ kk u
  have hP : ∀ z, (∏ᶠ u, (· - u) ^ d u : ℂ → ℂ) z = q z ^ m := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S), Finset.prod_apply, ← Finset.prod_pow]
    · refine Finset.prod_congr rfl fun u hu => ?_
      rw [hkk u (hSU u hu), zpow_natCast, mul_comm, pow_mul]
      rfl
    · intro u hu
      rw [Set.Finite.coe_toFinset]
      rw [Function.mem_mulSupport] at hu
      rw [Function.mem_support]
      intro h0
      apply hu
      rw [h0, zpow_zero]
  have hqd : Differentiable ℂ q := by
    intro z
    simp only [q]
    fun_prop
  have hgball : DifferentiableOn ℂ g (ball c R) :=
    (hg.mono ball_subset_closedBall).differentiableOn
  obtain ⟨s, hs, hsm⟩ := exists_root_of_ne_zero g m c R hm hgball
    (fun z hz => hgne ⟨z, ball_subset_closedBall hz⟩) hR
  refine ⟨fun z => q z * s z, hqd.differentiableOn.mul hs, ?_⟩
  intro z hz
  rw [mul_pow, hsm z hz]
  have hzU : z ∈ U := ball_subset_closedBall hz
  have hA := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hgeq) z hzU
  have hUn : U ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds
    (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hev : h =ᶠ[𝓝[≠] z] fun w => q w ^ m * g w := by
    filter_upwards [hA, hUn] with w hw hwU
    rcases hw with hw | hw
    · simp only [Set.mem_setOf_eq, Pi.smul_apply', smul_eq_mul] at hw
      rw [hw, hP]
    · exact absurd hwU hw
  have t1 : Tendsto h (𝓝[≠] z) (𝓝 (h z)) :=
    (hh z hzU).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => q w ^ m * g w) (𝓝[≠] z) (𝓝 (q z ^ m * g z)) :=
    (((hqd z).continuousAt.pow m).mul (hg z hzU).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique_of_eventuallyEq t2 t1 hev.symm)

end GlobalTheory.KZ.RootDisc
