import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import Development.AutomorphicArithmetic.ThickFrames.expectationSpec
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTops

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

private theorem UpperTheory.BernoulliSumsFrobeniusOrbits.bernoulliExpectation_le_of_monotone (p : ℕ → ℝ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A : Finset ℕ) :
    ∀ f : Finset ℕ → ℝ, Monotone f → (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) →
      exP p A f ≤ GlobalTheory.RandomTops.ex δ A f := by
  induction A using Finset.induction_on with
  | empty =>
    intro f _ _
    rw [GlobalTheory.RandomTops.ex_empty]
    simp [exP]
  | insert a S ha ih =>
    intro f hf hp
    have hpS : ∀ b ∈ S, 0 ≤ p b ∧ p b ≤ δ := fun b hb => hp b (Finset.mem_insert_of_mem hb)
    obtain ⟨hpa0, hpa1⟩ := hp a (Finset.mem_insert_self _ _)
    have e1 := ih f hf hpS
    have e2 := ih (fun T => f (insert a T))
      (fun T U hTU => hf (Finset.insert_subset_insert a hTU)) hpS
    have e3 : GlobalTheory.RandomTops.ex δ S f ≤ GlobalTheory.RandomTops.ex δ S (fun T => f (insert a T)) :=
      GlobalTheory.RandomTops.ex_mono h0 h1 fun T _ => hf (Finset.subset_insert a T)
    rw [(UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec p).2.2.2.2.1 a S f ha, GlobalTheory.RandomTops.ex_insert ha]
    have k1 := mul_le_mul_of_nonneg_left e1 (show 0 ≤ 1 - p a by linarith)
    have k2 := mul_le_mul_of_nonneg_left e2 hpa0
    have k3 := mul_le_mul_of_nonneg_left e3 (show 0 ≤ δ - p a by linarith)
    linarith

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.tail_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (A : Finset ℕ) (G K : ℕ), (∀ a ∈ A, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → A.card ≤ G →
      exP p A (fun T => ind (K ≤ T.card)) ≤ (G.choose K : ℝ) * δ ^ K ∧ exP p A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  intro p δ A G K hp h0 h1 hG
  have hmono : Monotone (fun T : Finset ℕ => ind (K ≤ T.card)) := by
    intro T U hTU
    have hc := Finset.card_le_card hTU
    simp only [ind]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have hle := UpperTheory.BernoulliSumsFrobeniusOrbits.bernoulliExpectation_le_of_monotone p δ h0 h1 A _ hmono hp
  exact ⟨le_trans hle (GlobalTheory.RandomTops.tail_le_choose h0 h1 hG K),
    le_trans hle (GlobalTheory.RandomTops.tail_le_binUpper h0 h1 hG K)⟩
