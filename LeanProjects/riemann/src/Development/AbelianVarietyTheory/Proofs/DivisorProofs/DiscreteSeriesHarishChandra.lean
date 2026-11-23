import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Finset

namespace GlobalTheory.DSParam

open Finset in
private theorem diagonal_exp_single_two_pi_eq_one {n : ℕ} (a : Fin n) :
    (Matrix.diagonal fun b ↦
      Complex.exp (↑((Pi.single a (2 * Real.pi) : Fin n → ℝ) b) * Complex.I)) = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp [Complex.exp_two_pi_mul_I]
  · simp [Pi.single_apply, h]

open Finset in
private theorem exists_int_eq_weight_of_isWtOn {n : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ K)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : _root_.Formalism.MainNotions.S.IsWtOn K σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  unfold _root_.Formalism.MainNotions.S.IsWtOn at hv
  have h1 := hv 0 (by simpa using hK)
  have h2 := hv (Pi.single a (2 * Real.pi)) (by rw [diagonal_exp_single_two_pi_eq_one]; exact hK)
  rw [diagonal_exp_single_two_pi_eq_one] at h2
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Matrix.diagonal_one, mul_zero, Finset.sum_const_zero, one_smul] at h1
  rw [h1] at h2
  have hsum : (∑ b, μ b * (Pi.single a (2 * Real.pi) : Fin n → ℝ) b) = μ a * (2 * Real.pi) := by
    simp [Pi.single_apply, mul_ite]
  rw [hsum] at h2
  have he : Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hv0
    have : (Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have : ((μ a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast this

open Finset in
private theorem one_mem_Kset_divisor {n : ℕ} (ε : Fin n → Bool) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.Formalism.REAL.Kset ε := by
  unfold _root_.Formalism.REAL.Kset
  exact ⟨one_mem _, by simp⟩

open Finset in
private theorem card_same_diff_sign_lt_gt_add_one_eq {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    #{b | a < b ∧ ε b = ε a} + #{b | b < a ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a}
      + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ b, ((if a < b ∧ ε b = ε a then 1 else 0) + (if b < a ∧ ε b = ε a then 1 else 0) +
      (if a < b ∧ ε b ≠ ε a then 1 else 0) + (if b < a ∧ ε b ≠ ε a then 1 else 0) : ℕ)
      = if b = a then 0 else 1 := by
    intro b
    rcases lt_trichotomy a b with h | h | h
    · have h1 : b ≠ a := ne_of_gt h
      have h2 : ¬ b < a := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
    · subst h; simp
    · have h1 : b ≠ a := ne_of_lt h
      have h2 : ¬ a < b := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
  rw [Finset.sum_congr rfl (fun b _ => key b)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  have := a.isLt
  omega

open Finset in
private theorem exists_int_rhoC_sub_rhoN_sub_half {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    ∃ m : ℤ, _root_.Formalism.REAL.rhoC ε a - _root_.Formalism.REAL.rhoN ε a - ((n : ℝ) - 1) / 2 = m := by
  have h := card_same_diff_sign_lt_gt_add_one_eq ε a
  unfold _root_.Formalism.REAL.rhoC _root_.Formalism.REAL.rhoN
  refine ⟨-((#{b | b < a ∧ ε b = ε a} : ℕ) + (#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℤ), ?_⟩
  have hr : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + #{b | b < a ∧ ε b = ε a}
      + #{b | a < b ∧ ε b ≠ ε a} + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
    exact_mod_cast h
  push_cast
  linear_combination hr / 2

open Finset in

theorem _root_.GlobalTheory.DSParam.isHCParam_of_isDS : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    StrictAnti lam → _root_.Formalism.MainNotions.S.IsDS ε lam σ → _root_.Formalism.QuantumDeterminants.IsHCParam lam := by
  intro n H _ _ ε lam σ hlam hds
  unfold _root_.Formalism.MainNotions.S.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  unfold _root_.Formalism.MainNotions.S.IsKTypeOf at hS
  obtain ⟨-, -, -, ⟨v, -, hv0, hv⟩, -⟩ := hS
  unfold _root_.Formalism.QuantumDeterminants.IsHCParam
  refine ⟨hlam, fun a => ?_⟩
  obtain ⟨k, hk⟩ := exists_int_eq_weight_of_isWtOn (one_mem_Kset_divisor ε) hv0 hv a
  obtain ⟨m, hm⟩ := exists_int_rhoC_sub_rhoN_sub_half ε a
  refine ⟨k + m, ?_⟩
  have hl : _root_.Formalism.QuantumDeterminants.lowK ε lam a = lam a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  push_cast
  linarith

end GlobalTheory.DSParam
