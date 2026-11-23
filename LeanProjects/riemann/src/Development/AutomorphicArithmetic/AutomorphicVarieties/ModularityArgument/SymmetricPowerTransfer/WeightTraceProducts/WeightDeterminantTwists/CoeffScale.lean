import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts

open Polynomial UpperTheory.V.Z.Sym.Wt

open MvPolynomial in
private theorem coeff_scale {σ : Type} [Fintype σ] (t : σ → ℂ) (P : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun p => MvPolynomial.C (t p) * MvPolynomial.X p) P : MvPolynomial σ ℂ) = (∏ p, t p ^ m p) * coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have : (aeval (fun p => MvPolynomial.C (t p) * MvPolynomial.X p) (MvPolynomial.monomial u a) : MvPolynomial σ ℂ) =
        MvPolynomial.C (∏ p, t p ^ u p) * MvPolynomial.monomial u a := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
      ring
    rw [this, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

open MvPolynomial in
private theorem eval_scale {σ : Type} (t x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (aeval (fun p => MvPolynomial.C (t p) * MvPolynomial.X p) P : MvPolynomial σ ℂ) =
      MvPolynomial.eval (fun p => t p * x p) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem UpperTheory.V.Z.Sym.Wt.memMH :
    UpperTheory.V.Z.Sym.Wt.MemMH := by
  intro K _ d n P
  classical
  have e : ∀ (s : K → ℂ) (m : K × Fin d →₀ ℕ), ∏ p : K × Fin d, s p.1 ^ m p = ∏ k, s k ^ ∑ i, m (k, i) := fun s m => by
    rw [Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum _ (fun i => m (k, i)) (s k)
  constructor
  · intro h m hm k
    have h1 : (MvPolynomial.aeval (fun p : K × Fin d => MvPolynomial.C (Function.update (fun _ => (1 : ℂ)) k 2 p.1) * MvPolynomial.X p) P :
        MvPolynomial (K × Fin d) ℂ) = MvPolynomial.C (∏ v, Function.update (fun _ => (1 : ℂ)) k 2 v ^ n v) * P :=
      MvPolynomial.funext fun x => by rw [eval_scale, map_mul, MvPolynomial.eval_C]; exact h _ x
    have h2 := congrArg (MvPolynomial.coeff m) h1
    rw [coeff_scale, MvPolynomial.coeff_C_mul, e] at h2
    have h3 := mul_right_cancel₀ (MvPolynomial.mem_support_iff.1 hm) h2
    have h4 : ∀ a : K → ℕ, ∏ v, Function.update (fun _ => (1 : ℂ)) k 2 v ^ a v = 2 ^ a k := fun a => by
      rw [Finset.prod_eq_single k] <;> simp +contextual [Function.update_of_ne]
    rw [h4, h4] at h3
    exact Nat.pow_right_injective le_rfl (by exact_mod_cast h3)
  · intro h s x
    rw [← eval_scale, ← MvPolynomial.eval_C (f := x) (∏ v, s v ^ n v), ← map_mul]
    congr 1
    ext m
    rw [coeff_scale, MvPolynomial.coeff_C_mul, e]
    by_cases hm : m ∈ P.support
    · simp only [h m hm]
    · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero, mul_zero]
