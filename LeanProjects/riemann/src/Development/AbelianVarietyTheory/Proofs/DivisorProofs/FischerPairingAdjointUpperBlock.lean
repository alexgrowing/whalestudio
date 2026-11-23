import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.ActSFirstBlock

open GlobalTheory.DefLift.BilFischer

theorem pair_comm {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp; ring
      · simp [e, Ne.symm e]

theorem pair_pderiv {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (X v * B) := by
  rw [pair_comm, ← pair_mul_X, pair_comm, mul_comm]

theorem pair_X_mul {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (X v * A) B = pair A (pderiv v B) := by
  rw [mul_comm, pair_mul_X]

theorem omE_neg {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (F : Pol p q r s) :
    omE u v F = -(X v * pderiv u F) - (if u = v then (1 / 2 : ℂ) else 0) • F := by
  have : omE u v F = -(pderiv u (X v * F)) + (if u = v then (1 / 2 : ℂ) else 0) • F := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases e : u = v
  · subst e
    simp only [if_true, smul_eq_mul, mul_one]
    module
  · simp [e, Ne.symm e]

theorem pderiv_aeval {σ τ : Type} [Fintype σ] (m : σ → MvPolynomial τ ℂ) (v : τ) (G : MvPolynomial σ ℂ) :
    pderiv v (aeval m G) = ∑ i, aeval m (pderiv i G) * pderiv v (m i) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add A B h h' => simp only [map_add, h, h', add_mul, Finset.sum_add_distrib]
  | mul_X A u h =>
    simp only [map_mul, aeval_X, Derivation.leibniz, h, smul_eq_mul, map_add, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem pderiv_detS (P Q S : ℕ) (h : Q ≤ S) (a : Fin P) (c : Ix 0 S) :
    pderiv (Sum.inl a, c) (detS P Q S h) = 0 := by
  classical
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have : detS P Q S h = aeval (fun i => X (g i)) (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this, pderiv_aeval]
  simp [g, pderiv_X, Pi.single_apply]

theorem pderiv_mS (P Q S : ℕ) (a a' : Fin P) (c : Fin S) (b : Fin Q) :
    pderiv (Sum.inl a', Sum.inr c) (mS P Q S a b) =
      if a = a' then X (Sum.inr b, Sum.inr c) else 0 := by
  classical
  simp only [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Prod.mk.injEq,
    Sum.inl.injEq, Sum.inr.injEq]
  split_ifs with e
  · simp [e]
  · simp [e]

theorem euler_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) :
    ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * pderiv (Sum.inl a', Sum.inr c) (embS P Q S h k' G) =
      embS P Q S h k' (∑ b, X (a, b) * pderiv (a', b) G) := by
  classical
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    Derivation.leibniz, Derivation.leibniz_pow, pderiv_detS, smul_zero, zero_add, smul_eq_mul,
    pderiv_aeval, pderiv_mS, map_sum, map_mul, aeval_X, Fintype.sum_prod_type, mul_zero, mul_ite,
    Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin P))), Finset.sum_ite_eq', Finset.mem_univ, if_true, mS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem pair_act_first_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  intro P Q S h k' a a' G f
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [omE_neg (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add, map_sum, map_sub, map_neg, map_smul, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, pair_X_mul, pair_pderiv,
    opS, Module.End.mul_apply, LinearMap.mulLeft_apply, Module.End.one_apply]
  have key := congrArg (pair f) (euler_embS P Q S h k' a a' G)
  simp only [map_sum] at key
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, key]
  by_cases e : a = a'
  · simp [e]
    ring
  · simp [e]

end GlobalTheory.CharPair.ActSFirstBlock

end
