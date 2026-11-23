import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagCase

theorem dualIdx_lt' {ρ k a : ℕ} (h : a < 2 * ρ + k + 1) : dualIdx ρ k a < 2 * ρ + k + 1 := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_iff' {ρ k a b : ℕ} (ha : a < 2 * ρ + k + 1) (hb : b < 2 * ρ + k + 1) :
    a = dualIdx ρ k b ↔ b = dualIdx ρ k a := by
  unfold dualIdx; split_ifs <;> omega

theorem mul_flagGram_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (A * flagGram K (2 * ρ + k + 1) ρ k) i j =
      A i ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩ * (if dualIdx ρ k j.val = ρ + k then -1 else 1) := by
  rw [mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩]
  · simp only [flagGram, Fin.val_mk]
    rw [if_pos ((dualIdx_iff' j.2 (dualIdx_lt' j.2)).mpr rfl)]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, mul_zero]
    intro h
    exact hl (Fin.ext ((dualIdx_iff' j.2 l.2).mp h))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagGram_mul_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (flagGram K (2 * ρ + k + 1) ρ k * A) i j =
      (if i.val = ρ + k then -1 else 1) * A ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩ j := by
  rw [mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩]
  · simp only [flagGram, Fin.val_mk, if_true]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagCond_dual_unipSym : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
    (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
    FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) →
    FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' hrel hM hM'
  subst hn

  have hkey : (M' : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)ᵀ * flagGram K (2 * ρ + k + 1) ρ k =
      flagGram K (2 * ρ + k + 1) ρ k * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) := by
    have h := congrArg (· * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) hrel
    simp only [Matrix.mul_assoc] at h
    rw [← h, Units.mul_inv, Matrix.mul_one]

  have hN : ∀ p q : Fin (2 * ρ + k + 1), ρ + k < p.val → q.val ≤ p.val →
      ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro p q hp hq
    have hp2 := p.2
    have hq2 := q.2
    have h1 := congrFun (congrFun hkey ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩) q
    rw [mul_flagGram_apply, flagGram_mul_apply, transpose_apply] at h1
    have e1 : (⟨dualIdx ρ k (dualIdx ρ k p.val), dualIdx_lt' (dualIdx_lt' p.2)⟩ : Fin (2 * ρ + k + 1)) = p :=
      Fin.ext ((dualIdx_iff' p.2 (dualIdx_lt' p.2)).mpr rfl).symm
    have hs : (if dualIdx ρ k p.val = ρ + k then (-1 : K) else 1) = 1 :=
      if_neg (by unfold dualIdx; split_ifs <;> omega)
    simp only [Fin.val_mk] at h1
    rw [e1, hs, one_mul] at h1
    have hc := hM'.1 ⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
    simp only [Matrix.sub_apply, sub_eq_zero] at hc
    rw [← h1, hc]
    by_cases hpq : p = q
    · subst hpq
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, hs, one_mul]
    · have hne : (⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ : Fin (2 * ρ + k + 1)) ≠ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩ := by
        intro h
        apply hpq
        have h' := congrArg Fin.val h
        simp only [Fin.val_mk] at h'
        apply Fin.ext
        unfold dualIdx at h'
        split_ifs at h' <;> omega
      rw [Matrix.one_apply_ne hne, zero_mul, Matrix.one_apply_ne hpq]

  have hMrow : ∀ t, ∀ p q : Fin (2 * ρ + k + 1), p.val + t = 2 * ρ + k → ρ + k < p.val → q.val ≤ p.val →
      (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro p q ht hp hq
      have hNM : (((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) * (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
        rw [Units.inv_mul]
      rw [mul_apply, Finset.sum_eq_single p] at hNM
      · rw [hN p p hp le_rfl, Matrix.one_apply_eq, one_mul] at hNM
        exact hNM
      · intro l _ hl
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hl) with h | h
        · rw [hN p l hp (le_of_lt h), Matrix.one_apply_ne (fun e => hl (e.symm)), zero_mul]
        · have hl2 := l.2
          rw [ih (2 * ρ + k - l.val) (by omega) l q (by omega) (by omega) (by omega),
            Matrix.one_apply_ne (fun e => by rw [e] at h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hall : ∀ i j : Fin (2 * ρ + k + 1), j.val ≤ i.val → (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j := by
    intro i j hji
    have hi2 := i.2
    by_cases h1 : j.val < ρ
    · have h := hM.1 i j h1 hji
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    by_cases h2 : j.val < ρ + k
    · have h := hM.2.2 i j (by omega) h2 hji
      simp only [Matrix.sub_apply, one_mul, sub_eq_zero] at h
      exact h
    by_cases h3 : j.val = ρ + k
    · have h := hM.2.1 i j h3 (by omega)
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    · exact hMrow (2 * ρ + k - i.val) i j (by omega) (by omega) hji
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.val < i.val := hij
    rw [hall i j (le_of_lt hij'), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
  · rw [hall i i le_rfl, Matrix.one_apply_eq]
  · have h := hM.2.1 i j h2 h0
    simp only [Matrix.sub_apply, sub_eq_zero] at h
    rw [h, Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

end GlobalTheory.FlagCase
