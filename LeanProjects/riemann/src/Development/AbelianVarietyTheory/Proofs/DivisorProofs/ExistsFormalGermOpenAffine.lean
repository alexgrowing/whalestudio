import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegRegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem liftAll_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) →
    deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftAll, deg]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih' := ih (fun x hx => hL x (by simp [hx]))
    have hcons : liftAll q l (p :: L) = (if l ∣ p.1 then liftL q l [p]
        else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++ liftAll q l L := by
      simp [liftAll, List.flatMap_cons]
    have hdegapp : ∀ A B : List (ℕ × ℕ), deg (A ++ B) = deg A + deg B := by intro A B; simp [deg]
    have hdegcons : deg (p :: L) = p.1 + deg L := by simp [deg]
    rw [hcons, hdegapp, hdegcons]
    by_cases h : l ∣ p.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [p] hq hl.pos (by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, h, hp.2⟩)
      rw [if_pos h]
      have hs : deg [p] = p.1 := by simp [deg]
      refine ⟨by rw [h1, hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · exact ih'.2 x hx
    · rw [if_neg h]
      have hr := (GlobalTheory.T.regular_pair_lift_to_prime_power_field q l p.1 p.2 hq hl hp.1 h hp.2).1
      have hs : deg [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] = p.1 := by simp [deg]
      refine ⟨by rw [hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, hr⟩
      · exact ih'.2 x hx

end GlobalTheory
