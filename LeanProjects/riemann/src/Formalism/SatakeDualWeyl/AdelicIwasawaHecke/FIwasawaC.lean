import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaB

open Formalism.UG Matrix

namespace Formalism.UG.P

macro "fIwasawa_omega" : tactic =>
  `(tactic| ((try simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.ext_iff,
    ne_eq, not_true_eq_false] at *) <;> omega))

section FIwasawaRed

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

def fIwasawaTri (r : ℕ) (M : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ i j : Fin n, j.val < r → j < i → M i j = 0

def fIwasawaKm (M : Matrix (Fin n) (Fin n) L) : Prop := fIwasawaUn σ M ∧ fIwasawaInt M

private theorem antiJ_apply_adelic_iwasawa_hecke (i j : Fin n) :
    antiJ L n i j = if (i : ℕ) + j + 1 = n then 1 else 0 := rfl

private theorem mul_antiJ_apply' (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (N * antiJ L n) i j = N i (Fin.rev j) := by
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · rw [antiJ_apply_adelic_iwasawa_hecke, if_pos (by rw [Fin.val_rev]; omega), mul_one]
  · intro k _ hk
    have hk' := k.isLt
    rw [antiJ_apply_adelic_iwasawa_hecke, if_neg, mul_zero]
    intro h
    apply hk
    ext
    rw [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem antiJ_mul_apply' (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (antiJ L n * N) i j = N (Fin.rev i) j := by
  have hi := i.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [antiJ_apply_adelic_iwasawa_hecke, if_pos (by rw [Fin.val_rev]; omega), one_mul]
  · intro k _ hk
    have hk' := k.isLt
    rw [antiJ_apply_adelic_iwasawa_hecke, if_neg, zero_mul]
    intro h
    apply hk
    ext
    rw [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem cT_apply_eq_sigma_transpose (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    cT σ N i j = σ (N j i) := rfl

private theorem cT_mul_reverse (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one_eq_one : cT σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  rw [cT_apply_eq_sigma_transpose]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]

private theorem antiJ_mul_antiJ : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul_apply', antiJ_apply_adelic_iwasawa_hecke, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [Fin.val_rev, ← h]; omega)]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    ext
    rw [Fin.val_rev] at h'
    omega

theorem fIwasawa_Km_mul {A B : Matrix (Fin n) (Fin n) L} (hA : fIwasawaKm σ A) (hB : fIwasawaKm σ B) :
    fIwasawaKm σ (A * B) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt at *
  obtain ⟨hAu, hAi⟩ := hA
  obtain ⟨hBu, hBi⟩ := hB
  refine ⟨?_, fun i j => ?_⟩
  · calc cT σ (A * B) * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B := by
          rw [cT_mul_reverse]
          simp only [Matrix.mul_assoc]
      _ = antiJ L n := by rw [hAu, hBu]
  · rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hAi i k) (hBi k j)

theorem fIwasawa_Km_one : fIwasawaKm σ (1 : Matrix (Fin n) (Fin n) L) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt
  refine ⟨by rw [cT_one_eq_one, Matrix.one_mul, Matrix.mul_one], fun i j => ?_⟩
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le'

theorem fIwasawa_Km_inv (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {A : Matrix (Fin n) (Fin n) L}
    (hA : fIwasawaKm σ A) : fIwasawaKm σ (fIwasawaInv σ A) := by
  unfold fIwasawaKm at hA ⊢
  obtain ⟨hAu, hAi⟩ := hA
  have hu := hAu
  unfold fIwasawaUn at hu
  have hBA : fIwasawaInv σ A * A = 1 := by
    unfold fIwasawaInv
    calc antiJ L n * cT σ A * antiJ L n * A = antiJ L n * (cT σ A * antiJ L n * A) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, antiJ_mul_antiJ]
  have hAB : A * fIwasawaInv σ A = 1 := mul_eq_one_comm.mp hBA
  refine ⟨?_, ?_⟩
  · unfold fIwasawaUn
    calc cT σ (fIwasawaInv σ A) * antiJ L n * fIwasawaInv σ A
        = cT σ (fIwasawaInv σ A) * (cT σ A * antiJ L n * A) * fIwasawaInv σ A := by rw [hu]
      _ = cT σ (A * fIwasawaInv σ A) * antiJ L n * (A * fIwasawaInv σ A) := by
          rw [cT_mul_reverse]
          simp only [Matrix.mul_assoc]
      _ = antiJ L n := by rw [hAB, cT_one_eq_one, Matrix.one_mul, Matrix.mul_one]
  · unfold fIwasawaInt at hAi ⊢
    intro i j
    unfold fIwasawaInv
    rw [mul_antiJ_apply', antiJ_mul_apply', cT_apply_eq_sigma_transpose, hσv]
    exact hAi _ _

theorem fIwasawa_gram_un (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (a b : Fin n) :
    ∑ j, σ (M (Fin.rev j) a) * M j b = if b = Fin.rev a then 1 else 0 := by
  unfold fIwasawaUn at hM
  have h := congrFun (congrFun hM a) b
  rw [Matrix.mul_apply] at h
  simp only [mul_antiJ_apply', cT_apply_eq_sigma_transpose, antiJ_apply_adelic_iwasawa_hecke] at h
  rw [h]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : b = Fin.rev a
  · rw [if_pos, if_pos hab]
    rw [hab, Fin.val_rev]
    omega
  · rw [if_neg, if_neg hab]
    intro h'
    apply hab
    ext
    rw [Fin.val_rev]
    omega

private theorem sigma_diag_mul_rev_diag_and_rev_entries_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (m : ℕ) : ∀ s : Fin n, s.val = m → s.val < r →
      σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
        ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hsm hs
    have key : ∀ b : Fin n, b ≤ Fin.rev s →
        σ (M s s) * M (Fin.rev s) b = if b = Fin.rev s then 1 else 0 := by
      intro b hb
      rw [← fIwasawa_gram_un σ M hM s b, Finset.sum_eq_single (Fin.rev s)]
      · rw [Fin.rev_rev]
      · intro j _ hj
        have hne : Fin.rev j ≠ s := fun h => hj (by rw [← h, Fin.rev_rev])
        rcases lt_or_gt_of_ne hne with h | h
        · have hjs : (Fin.rev j).val < m := by
            rw [← hsm]
            exact h
          have hjr : (Fin.rev j).val < r := by omega
          have hjb : b < Fin.rev (Fin.rev j) := by
            have := b.isLt
            have := j.isLt
            have := s.isLt
            rw [Fin.rev_rev]
            rw [Fin.le_def, Fin.val_rev] at hb
            rw [Fin.lt_def, Fin.val_rev] at h
            rw [Fin.lt_def]
            omega
          have h0 := (ih _ hjs (Fin.rev j) rfl hjr).2 b hjb
          rw [Fin.rev_rev] at h0
          rw [h0, mul_zero]
        · rw [hT (Fin.rev j) s hs h, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h1 := key (Fin.rev s) le_rfl
    rw [if_pos rfl] at h1
    refine ⟨h1, fun b hb => ?_⟩
    have h2 := key b hb.le
    rw [if_neg (ne_of_lt hb)] at h2
    exact (mul_eq_zero.mp h2).resolve_left (left_ne_zero_of_mul_eq_one h1)

theorem fIwasawa_rows (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (s : Fin n) (hs : s.val < r) :
    σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
      ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  exact sigma_diag_mul_rev_diag_and_rev_entries_zero σ M hM r hT s.val s rfl hs

theorem fIwasawa_col_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (ρ : Fin n) (hρr : ρ.val = r) (hρ : ρ < Fin.rev ρ) :
    ∀ i, Fin.rev ρ < i → M i ρ = 0 := by
  intro i hi
  have hi' := i.isLt
  have hρ' := ρ.isLt
  have hs : (Fin.rev i).val < r := by
    rw [Fin.val_rev, ← hρr]
    rw [Fin.lt_def, Fin.val_rev] at hi
    omega
  have h := (fIwasawa_rows σ M hM r hT (Fin.rev i) hs).2 ρ (by rw [Fin.rev_rev]; exact lt_trans hρ hi)
  rwa [Fin.rev_rev] at h

theorem fIwasawa_iso (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (ρ : Fin n)
    (hρ : ρ < Fin.rev ρ) : ∑ j, σ (M (Fin.rev j) ρ) * M j ρ = 0 := by
  rw [fIwasawa_gram_un σ M hM ρ ρ, if_neg (ne_of_lt hρ)]

theorem fIwasawa_perm (ρ a : Fin n) (hρ : ρ < Fin.rev ρ) (ha1 : ρ ≤ a) (ha2 : a ≤ Fin.rev ρ)
    (haa : a ≠ Fin.rev a) :
    ∃ π : Equiv.Perm (Fin n), π ρ = a ∧ (∀ i, π (Fin.rev i) = Fin.rev (π i)) ∧
      (∀ i, (i < ρ ∨ Fin.rev ρ < i) → π i = i) := by
  have hρn := ρ.isLt
  have han := a.isLt
  by_cases haρ : a = Fin.rev ρ
  · subst haρ
    refine ⟨Equiv.swap ρ (Fin.rev ρ), Equiv.swap_apply_left _ _, fun i => ?_, fun i hi => ?_⟩
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> fIwasawa_omega
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> fIwasawa_omega
  · refine ⟨Equiv.swap ρ a * Equiv.swap (Fin.rev ρ) (Fin.rev a), ?_, fun i => ?_, fun i hi => ?_⟩
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> fIwasawa_omega
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> fIwasawa_omega
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> fIwasawa_omega

end FIwasawaRed

end Formalism.UG.P
