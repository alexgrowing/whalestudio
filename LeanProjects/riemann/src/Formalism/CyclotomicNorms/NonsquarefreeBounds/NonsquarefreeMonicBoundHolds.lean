import Formalism.CyclotomicNorms.StatementI

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

namespace Sqf

variable {K : Type} [Field K]

lemma coeff_monicOf_lt {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.2), zero_add, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (Fin.ext h).symm)) (by simp)]
  simp

lemma coeff_monicOf_ge {N : ℕ} (a : Fin N → K) (k : ℕ) (hk : N ≤ k) :
    (monicOf a).coeff k = if k = N then 1 else 0 := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by have := j.2; omega)), add_zero]

lemma natDegree_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt a), natDegree_X_pow]

lemma monic_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by
  unfold monicOf
  exact monic_X_pow_add (degree_sum_fin_lt a)

lemma monicOf_coeffs (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases lt_or_ge n m with h | h
  · exact coeff_monicOf_lt (fun i : Fin m => p.coeff i) ⟨n, h⟩
  · rw [coeff_monicOf_ge _ n h]
    split_ifs with hn
    · subst hn
      rw [← hd]
      exact hp.coeff_natDegree.symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma decomp (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) (hsq : ¬ Squarefree f) :
    ∃ P h : K[X], P.Monic ∧ h.Monic ∧ 1 ≤ P.natDegree ∧ P.coeff 0 ≠ 0 ∧ f = P * P * h := by
  unfold Squarefree at hsq
  push_neg at hsq
  obtain ⟨x, ⟨g, hg⟩, hx⟩ := hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hg)
  have hc : x.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hx0
  have hP : (x * C x.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hx0
  have hu : C x.leadingCoeff⁻¹ * C x.leadingCoeff = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have key : f = (x * C x.leadingCoeff⁻¹) * (x * C x.leadingCoeff⁻¹) *
      (C x.leadingCoeff * C x.leadingCoeff * g) := by
    rw [hg]
    linear_combination (-(x * x * g * (C x.leadingCoeff⁻¹ * C x.leadingCoeff + 1))) * hu
  refine ⟨x * C x.leadingCoeff⁻¹, C x.leadingCoeff * C x.leadingCoeff * g, hP,
    Monic.of_mul_monic_left (hP.mul hP) (by rw [← key]; exact hf), ?_, ?_, key⟩
  · by_contra hlt
    push_neg at hlt
    have h1 : x * C x.leadingCoeff⁻¹ = 1 := (Monic.natDegree_eq_zero hP).mp (by omega)
    exact hx (isUnit_iff_exists_inv.mpr ⟨_, h1⟩)
  · intro hz
    apply h0
    rw [key, mul_coeff_zero, mul_coeff_zero, hz]
    simp

lemma geo (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∀ k, k < N → (∑ d ∈ Icc 1 k, q ^ (N - d)) + 2 * q ^ (N - 1 - k) ≤ 2 * q ^ (N - 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have e1 : N - 1 - k = (N - 1 - (k + 1)) + 1 := by omega
    have e2 : N - (k + 1) = N - 1 - k := by omega
    rw [e2]
    rw [e1] at ih' ⊢
    rw [pow_succ] at ih' ⊢
    have hm := Nat.mul_le_mul_left (q ^ (N - 1 - (k + 1))) hq
    linarith

end Sqf

end Formalism.CyclotomicNorms
