import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormulaStatement
open NumberField

private theorem sum_log_emb (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
  simp only [norm_prod] at h
  rw [← Real.log_prod (fun σ _ => by simpa using hN)]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
    (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
  simp [← Complex.norm_ratCast]

private theorem log_nat_sum (n : ℕ) (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p = Real.log n := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  symm
  apply Finset.sum_subset hS
  intro p _ hp
  rw [Finsupp.notMem_support_iff.1 hp]
  simp

private theorem finsum_rat (q : ℚ) (hq : q ≠ 0) (t : ℝ) :
    ∑ᶠ p : ℕ, t * (((q.num.natAbs.factorization p : ℝ) - (q.den.factorization p : ℝ)) * Real.log p)
      = t * Real.log ((|q| : ℚ) : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := q.num.natAbs.primeFactors ∪ q.den.primeFactors)]
  · rw [← Finset.mul_sum]
    congr 1
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [log_nat_sum _ _ Finset.subset_union_left, log_nat_sum _ _ Finset.subset_union_right,
      ← Real.log_div (by simpa using hq) (by simp)]
    congr 1
    rw [Rat.cast_abs, Rat.cast_def q, abs_div, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]
  · intro p hp
    by_contra h
    apply hp
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at h
    have h1 : q.num.natAbs.factorization p = 0 := Finsupp.notMem_support_iff.1 h.1
    have h2 : q.den.factorization p = 0 := Finsupp.notMem_support_iff.1 h.2
    simp [h1, h2]

theorem UpperTheory.padic_log_sum_eq_archimedean :
    ∀ (K : Type) [Field K] [NumberField K] (b : K) (t : ℝ), b ≠ 0 → (∑ᶠ p : ℕ, @dite ℝ p.Prime (Classical.propDecidable _) (fun hp => (haveI : Fact p.Prime := ⟨hp⟩; ∑ᶠ j : K →+* ℂ_[p], -(t * Real.log ‖j b‖))) fun _ => 0) = t * ∑ τ : K →+* ℂ, Real.log ‖τ b‖ := by
  intro K _ _ b t hb
  have hN : Algebra.norm ℚ b ≠ 0 := Algebra.norm_ne_zero_iff.2 hb
  rw [sum_log_emb K b hb, ← finsum_rat _ hN t]
  congr 1
  funext p
  by_cases hp : p.Prime
  · rw [dif_pos hp]
    haveI : Fact p.Prime := ⟨hp⟩
    have h := GlobalTheory.T.p_adic_product_formula K p b hb
    rw [finsum_eq_sum_of_fintype] at h
    show ∑ᶠ j : K →+* ℂ_[p], -(t * Real.log ‖j b‖) = _
    rw [finsum_eq_sum_of_fintype, Finset.sum_neg_distrib, ← Finset.mul_sum, h,
      Nat.factorization_def _ hp, Nat.factorization_def _ hp, padicValRat_def, padicValInt]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    ring
  · rw [dif_neg hp]
    simp [Nat.factorization_eq_zero_of_not_prime _ hp]
