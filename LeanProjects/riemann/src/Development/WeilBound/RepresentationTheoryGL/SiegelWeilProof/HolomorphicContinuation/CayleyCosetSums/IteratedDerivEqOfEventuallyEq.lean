import Mathlib

noncomputable section

open Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

theorem iteratedDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (k : ℕ) :
    iteratedDeriv k f s = iteratedDeriv k g s := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by simpa using h) h.eq_of_nhds

theorem leib {U : Set ℂ} (hU : IsOpen U) : ∀ (j : ℕ) (h₁ h₂ : ℂ → ℂ), DifferentiableOn ℂ h₁ U → DifferentiableOn ℂ h₂ U →
    ∀ s ∈ U, iteratedDeriv j (fun z => h₁ z * h₂ z) s =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i h₁ s * iteratedDeriv (j - i) h₂ s := by
  intro j
  induction j with
  | zero => intro h₁ h₂ _ _ s _; simp
  | succ j ih =>
    intro h₁ h₂ hd₁ hd₂ s hs
    have hd₁' : DifferentiableOn ℂ (deriv h₁) U := hd₁.deriv hU
    have hd₂' : DifferentiableOn ℂ (deriv h₂) U := hd₂.deriv hU
    have hev : deriv (fun z => h₁ z * h₂ z) =ᶠ[𝓝 s] fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact deriv_mul ((hd₁.differentiableAt (hU.mem_nhds hz))) ((hd₂.differentiableAt (hU.mem_nhds hz)))
    rw [iteratedDeriv_succ', iteratedDeriv_eq_of_eventuallyEq hev]
    have hc₁ : ContDiffAt ℂ j (fun z => deriv h₁ z * h₂ z) s :=
      ((hd₁'.mul hd₂).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hc₂ : ContDiffAt ℂ j (fun z => h₁ z * deriv h₂ z) s :=
      ((hd₁.mul hd₂').contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top
    have hsplit : (fun z => deriv h₁ z * h₂ z + h₁ z * deriv h₂ z) =
        (fun z => deriv h₁ z * h₂ z) + (fun z => h₁ z * deriv h₂ z) := rfl
    rw [hsplit, iteratedDeriv_add hc₁ hc₂, ih _ _ hd₁' hd₂ s hs, ih _ _ hd₁ hd₂' s hs]
    have key := Finset.sum_choose_succ_mul (R := ℂ) (fun a b => iteratedDeriv a h₁ s * iteratedDeriv b h₂ s) j
    simp only [mul_assoc] at key ⊢
    rw [key, add_comm]
    congr 1
    all_goals
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      (try rw [← iteratedDeriv_succ']); (try rw [show j + 1 - i = j - i + 1 by omega])

end PositivityTheory.Rg.Sw.HSt
