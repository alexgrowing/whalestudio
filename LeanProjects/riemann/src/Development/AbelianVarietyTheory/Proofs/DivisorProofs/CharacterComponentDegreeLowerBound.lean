import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockLowDeg

open MvPolynomial Formalism.BasicNotions.TH

theorem isKC_Eab_diag {P Q : ℕ} (a : Ix P Q) : IsKC (Eab a a : Mat P Q) := by
  intro b c hbc
  simp only [Eab, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (hbc (by cases a <;> trivial)).elim
  · rfl

theorem trace_Eab_diag {P Q : ℕ} (a : Ix P Q) : (Eab a a : Mat P Q).trace = 1 := by
  simp [Eab, Matrix.trace_single_eq_same]

def cartanVal {P Q R S : ℕ} (a : Ix P Q) (α : Ln P Q R S →₀ ℕ) : ℂ :=
  ∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)

theorem coeff_cartan {P Q R S : ℕ} (a : Ix P Q) (β : Ln P Q R S →₀ ℕ) (f : Pol P Q R S) :
    coeff β (fockAct1 P Q R S (Eab a a) f) = cartanVal a β * coeff β f := by
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
    have e : (monomial α c : Pol P Q R S) = c • monomial α 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul, cartan1, smul_smul, coeff_smul, coeff_smul, coeff_monomial]
    simp only [smul_eq_mul, cartanVal]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

theorem lowerDeg : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ f ∈ GlobalTheory.KFixIrr.chiOne P Q R S x, f ≠ 0 →
    P * k + Q * k' ≤ f.totalDegree := by
  intro P Q R S x k k' hk hk' f hf hf0
  rw [GlobalTheory.KFixIrr.mem_chiOne] at hf
  obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hf0
  have hval : ∀ a : Ix P Q, cartanVal a α = (x : ℂ) := by
    intro a
    have h := congrArg (coeff α) (hf _ (isKC_Eab_diag a))
    rw [coeff_cartan, trace_Eab_diag, mul_one, coeff_smul, smul_eq_mul] at h
    exact mul_right_cancel₀ hα h
  have hkC : (x : ℂ) - ((R : ℂ) - S) / 2 = k := by
    have := congrArg (fun t : ℚ => (t : ℂ)) hk
    simpa [cPair] using this
  have hk'C : (x : ℂ) + ((R : ℂ) - S) / 2 = k' := by
    have := congrArg (fun t : ℚ => (t : ℂ)) hk'
    simpa [cPair] using this
  have hP : ∀ i : Fin P, k ≤ ∑ c : Fin R, α (Sum.inl i, Sum.inl c) := by
    intro i
    have h := hval (Sum.inl i)
    simp only [cartanVal, Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    have e : ((∑ c : Fin R, α (Sum.inl i, Sum.inl c) : ℕ) : ℂ) =
        ((∑ c : Fin S, α (Sum.inl i, Sum.inr c) + k : ℕ) : ℂ) := by
      push_cast
      linear_combination h + hkC
    have := Nat.cast_injective e
    omega
  have hQ : ∀ j : Fin Q, k' ≤ ∑ c : Fin S, α (Sum.inr j, Sum.inr c) := by
    intro j
    have h := hval (Sum.inr j)
    simp only [cartanVal, Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    have e : ((∑ c : Fin S, α (Sum.inr j, Sum.inr c) : ℕ) : ℂ) =
        ((∑ c : Fin R, α (Sum.inr j, Sum.inl c) + k' : ℕ) : ℂ) := by
      push_cast
      linear_combination h + hk'C
    have := Nat.cast_injective e
    omega
  have hle := MvPolynomial.le_totalDegree (mem_support_iff.mpr hα)
  refine le_trans ?_ hle
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type]
  have h1 : P * k ≤ ∑ i : Fin P, (∑ c : Fin R, α (Sum.inl i, Sum.inl c) +
      ∑ c : Fin S, α (Sum.inl i, Sum.inr c)) := by
    calc P * k = ∑ _i : Fin P, k := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => le_add_right (hP i)
  have h2 : Q * k' ≤ ∑ j : Fin Q, (∑ c : Fin R, α (Sum.inr j, Sum.inl c) +
      ∑ c : Fin S, α (Sum.inr j, Sum.inr c)) := by
    calc Q * k' = ∑ _j : Fin Q, k' := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => le_add_left (hQ j)
  exact add_le_add h1 h2

end GlobalTheory.FockLowDeg

end
