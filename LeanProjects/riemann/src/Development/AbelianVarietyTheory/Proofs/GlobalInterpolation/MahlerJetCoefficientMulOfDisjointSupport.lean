import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulStatement
open GlobalTheory.MomN

namespace GlobalTheory

theorem mahler_mul_of_disjoint_support :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
      (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T →
      (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) →
      (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) →
      (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧
      (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) →
        GlobalTheory.MomN.mahler u (fun z => F z * H z) N =
          GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
            GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  intro V _ _ ι' _ _ u F H hF hH S T hST hFS hHT
  constructor
  · intro N ⟨p, hp, hNp⟩
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    apply Finset.sum_eq_zero
    intro k _
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ h)
    have hpT : p ∉ T := fun h => hp (Finset.mem_union_right _ h)
    by_cases hk : k p = 0
    · rw [hHT _ ⟨p, hpT, by simp [hk, hNp]⟩, mul_zero]
    · rw [hFS _ ⟨p, hpS, hk⟩, zero_mul]
  · intro N hN
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    rw [Finset.sum_eq_single (fun p => if p ∈ S then N p else 0)]
    · have hfun : (fun i => N i - (fun p => if p ∈ S then N p else 0) i) =
          (fun p => if p ∈ T then N p else 0) := by
        funext p
        by_cases hS : p ∈ S
        · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
          simp only [hS, hT, if_true, if_false, Nat.sub_self]
        · by_cases hT : p ∈ T
          · simp only [hS, hT, if_true, if_false, Nat.sub_zero]
          · have h0 : N p = 0 := hN p (by simp [hS, hT])
            simp only [hS, hT, if_false, h0, Nat.sub_zero]
      exact congrArg (fun g => GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
        GlobalTheory.MomN.mahler u H g) hfun
    · intro k hk hne
      by_contra hprod
      have h1 : GlobalTheory.MomN.mahler u F k ≠ 0 := left_ne_zero_of_mul hprod
      have h2 : GlobalTheory.MomN.mahler u H (fun i => N i - k i) ≠ 0 := right_ne_zero_of_mul hprod
      apply hne
      funext p
      rw [Fintype.mem_piFinset] at hk
      have hkp : k p ≤ N p := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hk p))
      by_cases hS : p ∈ S
      · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
        have : N p - k p = 0 := by
          by_contra h
          exact h2 (hHT _ ⟨p, hT, h⟩)
        simp only [hS, if_true]
        omega
      · simp only [hS, if_false]
        by_contra h
        exact h1 (hFS _ ⟨p, hS, h⟩)
    · intro h
      exfalso
      apply h
      rw [Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_range]
      split_ifs <;> omega

end GlobalTheory
