import Formalism.NormUnitaryBounds.Statement

open MvPolynomial Finset

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.NU

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cnt {d : ℕ} (t : Fin d → σ) : σ →₀ ℕ := ∑ m, Finsupp.single (t m) 1

def fct (e : σ →₀ ℕ) : ℕ := ∏ i, (e i).factorial

def P {d : ℕ} (S : (Fin d → σ) → ℂ) : MvPolynomial σ ℂ := ∑ t, monomial (cnt t) (S t)

lemma coeff_P {d : ℕ} (S : (Fin d → σ) → ℂ) (e : σ →₀ ℕ) :
    coeff e (P S) = ∑ t, if cnt t = e then S t else 0 := by
  simp only [P, coeff_sum, coeff_monomial]

lemma prod_X_eq {R : Type*} [CommSemiring R] {d : ℕ} (t : Fin d → σ) :
    (∏ m, (X (t m) : MvPolynomial σ R)) = monomial (cnt t) 1 := by
  rw [cnt, monomial_sum_one]; rfl

lemma pow_sum_X (d : ℕ) :
    (∑ i, (X i : MvPolynomial σ ℕ)) ^ d = ∑ t : Fin d → σ, monomial (cnt t) 1 := by
  have : (∑ i, (X i : MvPolynomial σ ℕ)) ^ d = ∏ _m : Fin d, ∑ i, (X i : MvPolynomial σ ℕ) := by
    simp [Finset.prod_const]
  rw [this, Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [prod_X_eq]

lemma card_fib {d : ℕ} (e : σ →₀ ℕ) (he : ∑ i, e i = d) :
    (univ.filter fun t : Fin d → σ => cnt t = e).card * fct e = d.factorial := by
  have h := congrArg (coeff e) (pow_sum_X (σ := σ) d)
  rw [Finset.sum_pow_eq_sum_piAntidiag] at h
  have hk : ∀ k : σ → ℕ, (∏ i, (X i : MvPolynomial σ ℕ) ^ k i) =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
    intro k
    rw [Finsupp.equivFunOnFinite_symm_eq_sum, monomial_sum_one]
    simp [X_pow_eq_monomial]
  simp only [hk, coeff_sum, coeff_monomial] at h
  have hc : ∀ k : σ → ℕ, coeff e ((Nat.multinomial univ k : MvPolynomial σ ℕ) *
      monomial (Finsupp.equivFunOnFinite.symm k) 1) =
      if k = ⇑e then Nat.multinomial univ k else 0 := by
    intro k
    rw [← map_natCast (C : ℕ →+* MvPolynomial σ ℕ), C_mul_monomial, mul_one, coeff_monomial]
    by_cases hke : k = ⇑e
    · subst hke; simp
    · rw [if_neg hke, if_neg]
      intro h'; apply hke; rw [← h']; simp
  simp only [hc, Finset.sum_ite_eq', Finset.sum_boole] at h
  rw [if_pos (by simp [he])] at h
  rw [Nat.cast_id] at h
  rw [← h, mul_comm, fct, ← he]
  exact Nat.multinomial_spec _ _

def T (d : ℕ) (F : MvPolynomial σ ℂ) (t : Fin d → σ) : ℂ :=
  coeff (cnt t) F * (fct (cnt t) : ℂ) / (d.factorial : ℂ)

lemma rep {d : ℕ} (F : MvPolynomial σ ℂ) (hF : ∀ e ∈ F.support, ∑ i, e i = d) :
    P (T d F) = F := by
  ext e
  rw [coeff_P]
  have hsum : (∑ t : Fin d → σ, if cnt t = e then T d F t else 0)
      = ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) *
        (coeff e F * fct e / d.factorial) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_congr rfl (g := fun _ => coeff e F * fct e / d.factorial)]
    · simp
    · intro t ht
      simp only [T, (Finset.mem_filter.1 ht).2]
  rw [hsum]
  by_cases he : ∑ i, e i = d
  · have hc := card_fib e he
    have hc' : ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) * (fct e : ℂ) =
        d.factorial := by exact_mod_cast hc
    have hd : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
    calc ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) *
          (coeff e F * fct e / d.factorial)
        = coeff e F * (((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) * (fct e : ℂ))
          / d.factorial := by ring
      _ = coeff e F := by rw [hc', mul_div_assoc, div_self hd, mul_one]
  · have hz : coeff e F = 0 := by
      by_contra h
      exact he (hF e (mem_support_iff.2 h))
    simp [hz]

def ip (F G : MvPolynomial σ ℂ) : ℂ :=
  ∑ e ∈ F.support, coeff e F * star (coeff e G) * (fct e : ℂ)

def sub (V : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun i => ∑ l, C (V i l) * X l

def act {d : ℕ} (V : Matrix σ σ ℂ) (S : (Fin d → σ) → ℂ) (t : Fin d → σ) : ℂ :=
  ∑ s, S s * ∏ m, V (s m) (t m)

lemma sub_sub (V : Matrix σ σ ℂ) (hV : V * star V = 1) (F : MvPolynomial σ ℂ) :
    sub (star V) (sub V F) = F := by
  have key : (sub (star V)).comp (sub V) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, sub, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      AlgHom.id_apply]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum]
    have h2 : ∀ k, ∑ l, V i l * star V l k = (1 : Matrix σ σ ℂ) i k := fun k => by
      rw [← hV, Matrix.mul_apply]
    simp_rw [h2, Matrix.one_apply]
    simp
  simpa using AlgHom.congr_fun key F

def FR (F : MvPolynomial σ ℂ) : ℝ := ∑ e ∈ F.support, ‖coeff e F‖ ^ 2 * (fct e : ℝ)

lemma ip_self (F : MvPolynomial σ ℂ) : ip F F = (FR F : ℂ) := by
  simp only [ip, FR, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

def blk {N n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ :=
  fun p q => if p.1 = q.1 then U p.2 q.2 else 0

end Formalism.NormUnitaryCountingLemmas.NU

namespace Formalism.NormUnitaryCountingLemmas

end Formalism.NormUnitaryCountingLemmas
