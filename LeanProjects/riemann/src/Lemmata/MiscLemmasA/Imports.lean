import Mathlib

namespace Bl.SecondBlockLemmaB

theorem goal1 (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := by
  intro n
  induction n with
  | zero =>
    intro g _ _ _
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact i.elim0
  | succ n ih =>
    intro g hd hU hL'
    obtain ⟨u, hu⟩ : ∃ u : O, g (Fin.last n) (Fin.last n) * u = 1 := (hd _).exists_right_inv
    have hnl : ∀ i : Fin n, ¬ (Fin.last n < i.castSucc) :=
      fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
    have hcorr : ∀ i : Fin n,
        g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc ∈ U * L := fun i =>
      Ideal.mul_mem_mul (U.mul_mem_right _ (hU _ _ (Fin.castSucc_lt_last i)))
        (hL' _ _ (Fin.castSucc_lt_last i))
    have hAd : ∀ i : Fin n, IsUnit (g i.castSucc i.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc) := by
      intro i
      have h2 := hd i.castSucc
      rw [show g i.castSucc i.castSucc = (g i.castSucc i.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc)
        + g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc by ring] at h2
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h2 with h | h
      · exact h
      · exact absurd h (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
          (hL (Ideal.mul_le_right (hcorr i)))))
    have hAU : ∀ i j : Fin n, i < j → g i.castSucc j.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc ∈ U := by
      intro i j hij
      exact U.sub_mem (hU _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij))
        (U.mul_mem_right _ (U.mul_mem_right _ (hU _ _ (Fin.castSucc_lt_last i))))
    have hAL : ∀ i j : Fin n, j < i → g i.castSucc j.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc ∈ L := by
      intro i j hij
      exact L.sub_mem (hL' _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij))
        (L.mul_mem_left _ (hL' _ _ (Fin.castSucc_lt_last j)))
    obtain ⟨x', y', δ', hg, hx1, hx0, hxU, hδu, hδ, hy1, hy0, hyL⟩ :=
      ih (Matrix.of fun i j => g i.castSucc j.castSucc
        - g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc)
        (fun i => by simp only [Matrix.of_apply]; exact hAd i)
        (fun i j h => by simp only [Matrix.of_apply]; exact hAU i j h)
        (fun i j h => by simp only [Matrix.of_apply]; exact hAL i j h)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
        (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => O) (g i'.castSucc (Fin.last n) * u)
          (fun j' => x' i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
        (Fin.lastCases (motive := fun _ => O) 1 (fun j' => u * g (Fin.last n) j'.castSucc) j)
        (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => y' i' j') j) i,
      Fin.lastCases (motive := fun _ => O) (g (Fin.last n) (Fin.last n)) δ',
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp
          linear_combination (-(g (Fin.last n) j.castSucc)) * hu
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp
          linear_combination (-(g i.castSucc (Fin.last n))) * hu
        | cast j =>
          have := hg i j
          simp only [Matrix.of_apply] at this
          simp
          linear_combination this - (g i.castSucc (Fin.last n) * u * g (Fin.last n) j.castSucc) * hu
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp [hx1 i]
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd h (hnl i)
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hx0 i j (Fin.castSucc_lt_castSucc_iff.mp h)
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          exact U.mul_mem_right _ (hU _ _ (Fin.castSucc_lt_last i))
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hxU i j (Fin.castSucc_lt_castSucc_iff.mp h)
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact hd _
      | cast i => simp only [Fin.lastCases_castSucc]; exact hδu i
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i =>
        have h1 := hδ i
        simp only [Matrix.of_apply] at h1
        simp only [Fin.lastCases_castSucc]
        have e : δ' i - g i.castSucc i.castSucc = (δ' i - (g i.castSucc i.castSucc
            - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc))
            - g i.castSucc (Fin.last n) * u * g (Fin.last n) i.castSucc := by ring
        rw [e]
        exact (U * L).sub_mem h1 (hcorr i)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp [hy1 i]
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j => exact absurd h (hnl j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hy0 i j (Fin.castSucc_lt_castSucc_iff.mp h)
    · intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd h (lt_irrefl _)
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          exact L.mul_mem_left _ (hL' _ _ (Fin.castSucc_lt_last j))
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd h (hnl i)
        | cast j =>
          simp only [Matrix.of_apply, Fin.lastCases_castSucc]
          exact hyL i j (Fin.castSucc_lt_castSucc_iff.mp h)

end Bl.SecondBlockLemmaB
