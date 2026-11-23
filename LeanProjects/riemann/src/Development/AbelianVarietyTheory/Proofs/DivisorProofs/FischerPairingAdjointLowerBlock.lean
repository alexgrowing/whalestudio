import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.DefLift.BilFischer

namespace GlobalTheory.CharPair.SecondBlockS

theorem pair_symm' {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) : pair f g = pair g f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
    induction g using MvPolynomial.induction_on' with
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases h : α = β
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    | add g g' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | add f f' h h' => simp only [map_add, LinearMap.add_apply, h, h']

theorem pair_X_pderiv {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) (u v : σ) :
    pair (X u * pderiv v f) g = pair f (X v * pderiv u g) := by
  rw [mul_comm, pair_mul_X, pair_symm', ← pair_mul_X, pair_symm', mul_comm]

variable {P Q S : ℕ}

def rowD (b b' : Fin Q) : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
  ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)

theorem rowD_apply (b b' : Fin Q) (g : Pol P Q 0 S) :
    rowD b b' g = ∑ c : Fin S, X (Sum.inr b', Sum.inr c) * pderiv (Sum.inr b, Sum.inr c) g := by
  rw [rowD, PI.RL.W.derivation_sum_apply]
  simp [Derivation.smul_apply, smul_eq_mul]

theorem rowD_X_inr_inr (b b' i : Fin Q) (c : Fin S) :
    rowD b b' (X (Sum.inr i, Sum.inr c) : Pol P Q 0 S) =
      if i = b then X (Sum.inr b', Sum.inr c) else 0 := by
  rw [rowD_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero, Sum.inr.injEq]
  by_cases h : i = b
  · subst h
    simp
  · simp [h]

theorem rowD_u (b b' : Fin Q) (a : Fin P) (c : Fin S) :
    rowD b b' (X (Sum.inl a, Sum.inr c) : Pol P Q 0 S) = 0 := by
  rw [rowD_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowD_mS (b b' i : Fin Q) (a : Fin P) :
    rowD b b' (mS P Q S a i) = if i = b then mS P Q S a b' else 0 := by
  simp only [mS, map_sum, Derivation.leibniz, rowD_X_inr_inr, rowD_u, smul_zero, add_zero, smul_eq_mul]
  split_ifs <;> simp

theorem rowD_detS (h : Q ≤ S) (b b' : Fin Q) :
    rowD b b' (detS P Q S h) = if b = b' then detS P Q S h else 0 := by
  rw [detS, PI.RL.W.derivation_det, Finset.sum_eq_single b]
  · simp only [Matrix.of_apply, rowD_X_inr_inr, if_true]
    split_ifs with hb
    · subst hb
      congr 1
      exact Matrix.updateRow_eq_self _ b
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun b c : Fin Q =>
        (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) (Ne.symm hb)
  · intro i _ hi
    simp only [Matrix.of_apply, rowD_X_inr_inr, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem rowD_aeval (b b' : Fin Q) (G : Mdl P Q) :
    rowD b b' (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add G G' h h' => simp only [map_add, h, h', mul_add, Finset.sum_add_distrib]
  | mul_X G v h =>
    obtain ⟨a, i⟩ := v
    rw [map_mul, Derivation.leibniz, h, aeval_X, rowD_mS]
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, map_add, map_sum,
      map_mul, aeval_X, pderiv_X, Pi.single_apply, Prod.mk.injEq, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · by_cases hi : i = b
      · subst hi
        rw [Finset.sum_eq_single a]
        · simp [mul_comm]
        · intro x _ hx
          simp [Ne.symm hx]
        · simp
      · simp [hi]
    · exact Finset.sum_congr rfl fun _ _ => by ring

theorem rowD_embS (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q) :
    rowD b b' (embS P Q S h k' G) = embS P Q S h k' (∑ a, X (a, b') * pderiv (a, b) G) +
      (if b = b' then (k' : ℂ) else 0) • embS P Q S h k' G := by
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [Derivation.leibniz, rowD_aeval, Derivation.leibniz_pow, rowD_detS, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, add_comm, mul_comm]
  congr 1
  split_ifs
  · rcases k' with _ | k
    · simp
    · rw [Nat.cast_smul_eq_nsmul, mul_smul_comm, Nat.add_sub_cancel, ← pow_succ]
  · simp

theorem pair_fockAct1_inr_inr_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q)
    (f : Pol P Q 0 S) :
    pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inr b')) f) (embS P Q S h k' G) =
      pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G)) := by
  have e : embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G) =
      rowD b b' (embS P Q S h k' G) + (if b = b' then (S : ℂ) / 2 else 0) • embS P Q S h k' G := by
    rw [rowD_embS, opS]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    split_ifs
    · rw [add_smul, add_assoc]
    · simp
  rw [e, fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowD_apply]
  simp only [GlobalTheory.CompactHarm.omE_pp (Sum.inr _, Sum.inr _) (Sum.inr _, Sum.inr _) rfl rfl,
    Finset.univ_eq_empty, Finset.sum_empty, zero_add, map_sum, map_add, map_smul, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, pair_X_pderiv, Finset.sum_add_distrib,
    Prod.mk.injEq, Sum.inr.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul]
  refine congrArg₂ (· + ·) rfl ?_
  split_ifs
  · ring
  · simp

end GlobalTheory.CharPair.SecondBlockS

end
