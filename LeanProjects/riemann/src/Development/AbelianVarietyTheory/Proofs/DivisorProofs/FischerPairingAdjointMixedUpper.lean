import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

open GlobalTheory.DefLift.BilFischer in
private theorem pair_symm' {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp only [if_true]; ring
      · simp [e, Ne.symm e]

open GlobalTheory.DefLift.BilFischer in
private theorem pair_pderiv' {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (B * X v) := by
  rw [pair_symm', ← pair_mul_X, pair_symm']

theorem pair_fockAct1_embS_up : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inr b)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G)) := by
  intro P Q S h k' a b G f
  have hom : ∀ c : Fin S, omE ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (Sum.inr b, Sum.inr c) f =
      -(pderiv (Sum.inl a, Sum.inr c) (pderiv (Sum.inr b, Sum.inr c) f)) := by
    intro c
    have h1 : linePos ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) = false := rfl
    have h2 : linePos ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) = true := rfl
    simp [omE, raiB, lowB, h1, h2]
  have hE : embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G) =
      -(embS P Q S h k' G * mS P Q S a b) := by
    simp only [opS, embS, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, map_mul, aeval_X]
    ring
  rw [hE, fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, hom, map_sum, map_neg,
    LinearMap.sum_apply, LinearMap.neg_apply, pair_pderiv', mS, Finset.mul_sum,
    Finset.sum_neg_distrib, mul_assoc]

end GlobalTheory.CharPair
