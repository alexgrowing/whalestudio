import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Filter Topology

theorem exists_dominant_sub_smul (d : IndexData) (u w : Idx d → ℚ) (hu : IsRegular d (uR d u)) :
    ∃ s1 : ℝ, 0 < s1 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ s1 → IsDominant d (uR d (u - s • w)) := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 →
      0 < ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b)) := by
    rw [Filter.eventually_all]; intro τ
    rw [Filter.eventually_all]; intro a
    rw [Filter.eventually_all]; intro b
    by_cases hab : b.val = a.val + 1
    · have hpos : (0 : ℝ) < (u (τ, a) : ℝ) - u (τ, b) := hu τ a b hab
      have hc : Continuous fun t : ℝ =>
          ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b)) := by
        fun_prop
      have h0 : (0 : ℝ) <
          (fun t : ℝ => ((u (τ, a) : ℝ) - u (τ, b)) - t * ((w (τ, a) : ℝ) - w (τ, b))) 0 := by
        simpa using hpos
      filter_upwards [(hc.tendsto 0).eventually (lt_mem_nhds h0)] with t ht _ using ht
    · exact Filter.Eventually.of_forall fun _ h => absurd h hab
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, fun s hs hsle τ a b hab => ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd : dist (s : ℝ) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs']
    linarith
  have key := hball hd τ a b hab
  simp only [uR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  linarith

theorem TheoremTLower.proof (hL : LimitTheorem.Statement) : TheoremTLower.Statement := by
  intro d S u g B0 hyp _ hI1 hI2
  obtain ⟨C3, s0, hs0, hb⟩ := hI2
  obtain ⟨s1, hs1, hdom⟩ := exists_dominant_sub_smul d u S.shiftW hyp.1
  have key := hL (Idx d) (S.Ptwo B0) (fun p => (u p : ℝ)) (fun p => (S.shiftW p : ℝ))
    (S.Mbar B0 u) C3 (min s0 s1) (lt_min hs0 hs1) (by
      intro s hs hsle
      have h := hb s hs (le_trans hsle (min_le_left _ _))
        (hdom s hs (le_trans hsle (min_le_right _ _)))
      have hfun : (fun o : Option (Idx d) => o.elim (s : ℝ) (fun p => ((u - s • S.shiftW) p : ℝ))) =
          (fun o : Option (Idx d) => o.elim (s : ℝ) (fun p => (u p : ℝ) - s * (S.shiftW p : ℝ))) := by
        funext o
        cases o with
        | none => rfl
        | some p => simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rwa [hfun] at h)
  unfold bigP
  rw [← hI1 u]
  exact key

end GroundTheory.Heights₂.Heights.TheoremB
