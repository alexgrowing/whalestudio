import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr

open MvPolynomial Formalism.BasicNotions.TH

noncomputable section

namespace GlobalTheory.LowIrr

theorem coeff_fockAct1_diag {P Q R S : ℕ} (a : Ix P Q) (f : Pol P Q R S) (α : Ln P Q R S →₀ ℕ) :
    coeff α (fockAct1 P Q R S (Eab a a) f) =
      (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) * coeff α f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u r =>
    have e : (monomial u r : Pol P Q R S) = r • monomial u 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, cartan1, coeff_smul, coeff_smul, coeff_smul, coeff_monomial]
    by_cases h : u = α
    · subst h; simp; ring
    · simp [h]
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]

theorem eig_inl {P Q R S : ℕ} (i : Fin P) (α : Ln P Q R S →₀ ℕ) :
    (∑ c, lineSign (Sum.inl i : Ix P Q) c * (((α (Sum.inl i, c) : ℕ) : ℂ) + 1 / 2)) =
      ((∑ c : Fin R, α (Sum.inl i, Sum.inl c) : ℕ) : ℂ) - ((∑ d : Fin S, α (Sum.inl i, Sum.inr d) : ℕ) : ℂ)
        + ((R : ℂ) - S) / 2 := by
  rw [Fintype.sum_sum_type]
  simp only [lineSign, one_mul, neg_one_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sum]
  ring

theorem eig_inr {P Q R S : ℕ} (j : Fin Q) (α : Ln P Q R S →₀ ℕ) :
    (∑ c, lineSign (Sum.inr j : Ix P Q) c * (((α (Sum.inr j, c) : ℕ) : ℂ) + 1 / 2)) =
      ((∑ d : Fin S, α (Sum.inr j, Sum.inr d) : ℕ) : ℂ) - ((∑ c : Fin R, α (Sum.inr j, Sum.inl c) : ℕ) : ℂ)
        - ((R : ℂ) - S) / 2 := by
  rw [Fintype.sum_sum_type]
  simp only [lineSign, one_mul, neg_one_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sum]
  ring

theorem eig_eq_of_mem {P Q R S : ℕ} {x : ℚ} {f : Pol P Q R S} (hf : f ∈ GlobalTheory.KFixIrr.chiOne P Q R S x)
    (a : Ix P Q) {α : Ln P Q R S →₀ ℕ} (hα : α ∈ f.support) :
    (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (x : ℂ) := by
  have hKC : IsKC (Eab a a : Mat P Q) := by
    rcases a with a | a
    · exact eab_isKC_inl a a
    · exact eab_isKC_inr a a
  have h := congrArg (coeff α) ((GlobalTheory.KFixIrr.mem_chiOne x f).1 hf _ hKC)
  rw [coeff_fockAct1_diag, coeff_smul, Eab, Matrix.trace_single_eq_same, mul_one, smul_eq_mul] at h
  exact mul_right_cancel₀ (mem_support_iff.1 hα) h

theorem degree_of_mem {P Q R S : ℕ} {x : ℚ} {k k' : ℕ} (hx : x - cPair R S = k) (hx' : x + cPair R S = k')
    {f : Pol P Q R S} (hf : f ∈ GlobalTheory.KFixIrr.chiOne P Q R S x) {α : Ln P Q R S →₀ ℕ} (hα : α ∈ f.support) :
    α.degree = P * k + Q * k' + 2 * ((∑ i : Fin P, ∑ d : Fin S, α (Sum.inl i, Sum.inr d)) +
      ∑ j : Fin Q, ∑ c : Fin R, α (Sum.inr j, Sum.inl c)) := by
  have cx : (x : ℂ) - ((R : ℂ) - S) / 2 = k := by
    have := congrArg (fun q : ℚ => (q : ℂ)) hx
    simpa [cPair] using this
  have cx' : (x : ℂ) + ((R : ℂ) - S) / 2 = k' := by
    have := congrArg (fun q : ℚ => (q : ℂ)) hx'
    simpa [cPair] using this
  have hR : ∀ i : Fin P, ∑ c : Fin R, α (Sum.inl i, Sum.inl c) = k + ∑ d : Fin S, α (Sum.inl i, Sum.inr d) := by
    intro i
    have h := eig_eq_of_mem hf (Sum.inl i) hα
    rw [eig_inl] at h
    have : ((∑ c : Fin R, α (Sum.inl i, Sum.inl c) : ℕ) : ℂ) = ((k + ∑ d : Fin S, α (Sum.inl i, Sum.inr d) : ℕ) : ℂ) := by
      push_cast at h ⊢
      linear_combination h + cx
    exact_mod_cast this
  have hS : ∀ j : Fin Q, ∑ d : Fin S, α (Sum.inr j, Sum.inr d) = k' + ∑ c : Fin R, α (Sum.inr j, Sum.inl c) := by
    intro j
    have h := eig_eq_of_mem hf (Sum.inr j) hα
    rw [eig_inr] at h
    have : ((∑ d : Fin S, α (Sum.inr j, Sum.inr d) : ℕ) : ℂ) = ((k' + ∑ c : Fin R, α (Sum.inr j, Sum.inl c) : ℕ) : ℂ) := by
      push_cast at h ⊢
      linear_combination h + cx'
    exact_mod_cast this
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type]
  rw [Finset.sum_congr rfl fun i _ => congrArg (· + _) (hR i),
    Finset.sum_congr rfl fun j _ => congrArg (_ + ·) (hS j)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem lowShape : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'),
    (∀ l ∈ f.vars, Formalism.BasicNotions.TH.linePos l = true) ∧ f.IsHomogeneous (P * k + Q * k') := by
  intro P Q R S x k k' hx hx' f hf
  obtain ⟨hc, hdeg⟩ := (GlobalTheory.KFixIrr.mem_lowOne x _ f).1 hf
  have key : ∀ α ∈ f.support, ((∑ i : Fin P, ∑ d : Fin S, α (Sum.inl i, Sum.inr d)) = 0 ∧
      ∑ j : Fin Q, ∑ c : Fin R, α (Sum.inr j, Sum.inl c) = 0) ∧ α.degree = P * k + Q * k' := by
    intro α hα
    have h1 := degree_of_mem hx hx' hc hα
    have h2 : α.degree ≤ f.totalDegree := le_totalDegree hα
    omega
  refine ⟨fun l hl => ?_, fun d hd => ?_⟩
  · obtain ⟨α, hα, hl⟩ := mem_vars l |>.1 hl
    obtain ⟨⟨h1, h2⟩, -⟩ := key α hα
    rw [Finsupp.mem_support_iff] at hl
    rcases l with ⟨a | a, c | c⟩
    · rfl
    · exact absurd (Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 h1 a (Finset.mem_univ _)) c
        (Finset.mem_univ _)) hl
    · exact absurd (Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 h2 a (Finset.mem_univ _)) c
        (Finset.mem_univ _)) hl
    · rfl
  · rw [← (key d (mem_support_iff.2 hd)).2, Finsupp.degree_eq_weight_one]
    rfl

end GlobalTheory.LowIrr

end
