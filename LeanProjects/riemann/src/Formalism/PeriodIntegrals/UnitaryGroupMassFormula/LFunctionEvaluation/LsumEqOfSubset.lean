import Mathlib
import Formalism.PeriodIntegrals.WwEval

noncomputable section

namespace PI.WwEvalWork

open MvPolynomial

section Lsum

variable {σ K : Type*} [CommRing K]

def Lsum (w : (σ →₀ ℕ) → K) (Q : MvPolynomial σ K) : K :=
  ∑ α ∈ Q.support, coeff α Q * w α

lemma Lsum_eq_of_subset (w : (σ →₀ ℕ) → K) (Q : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : Lsum w Q = ∑ α ∈ S, coeff α Q * w α := by
  unfold Lsum
  apply Finset.sum_subset h
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Lsum_add (w : (σ →₀ ℕ) → K) (p q : MvPolynomial σ K) :
    Lsum w (p + q) = Lsum w p + Lsum w q := by
  classical
  rw [Lsum_eq_of_subset w (p + q) (p.support ∪ q.support) support_add,
    Lsum_eq_of_subset w p (p.support ∪ q.support) Finset.subset_union_left,
    Lsum_eq_of_subset w q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add, add_mul]

lemma Lsum_zero (w : (σ →₀ ℕ) → K) : Lsum w (0 : MvPolynomial σ K) = 0 := by
  simp [Lsum]

lemma Lsum_finset_sum {ι : Type*} (w : (σ →₀ ℕ) → K) (s : Finset ι)
    (f : ι → MvPolynomial σ K) : Lsum w (∑ i ∈ s, f i) = ∑ i ∈ s, Lsum w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lsum_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lsum_add, ih]

lemma Lsum_monomial (w : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (r : K) :
    Lsum w (monomial α r) = r * w α := by
  classical
  rw [Lsum_eq_of_subset w _ {α} support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

end Lsum

section Peval

variable {σ1 σ2 K : Type*} [CommRing K]

def peval (x : σ1 → K) : MvPolynomial (σ1 ⊕ σ2) ℤ →+* MvPolynomial σ2 K :=
  eval₂Hom (C.comp (Int.castRingHom K)) (Sum.elim (fun v => C (x v)) X)

lemma peval_monomial (x : σ1 → K) (μ : σ1 ⊕ σ2 →₀ ℕ) (c : ℤ) :
    peval x (monomial μ c) = monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).2
      ((c : K) * (Finsupp.sumFinsuppEquivProdFinsupp μ).1.prod fun v e => x v ^ e) := by
  conv_lhs => rw [← Finsupp.comapDomain_sumElim_comapDomain μ]
  rw [peval, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_sumElim]
  simp only [Finsupp.sumFinsuppEquivProdFinsupp_apply, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr]
  have h1 : ((Finsupp.comapDomain Sum.inl μ Sum.inl_injective.injOn).prod fun v e =>
      (C (x v) : MvPolynomial σ2 K) ^ e) =
      C ((Finsupp.comapDomain Sum.inl μ Sum.inl_injective.injOn).prod fun v e => x v ^ e) := by
    simp [Finsupp.prod, map_prod, map_pow]
  rw [h1, monomial_eq, C_mul, RingHom.comp_apply, eq_intCast, ← mul_assoc]

end Peval

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}

def wt (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (α : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    ℂ_[l] :=
  (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th

theorem eval_applyAt0 (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (x : Lt × ℕ × Fin N0 → ℂ_[l]) (P : MvPolynomial (PI.WwEval.KM.XZ Lt N0 N1) ℤ) :
    eval x (PI.WwEval.KM.applyAt0 N0 N1 l Th P) = Lsum (wt Th) (peval x P) := by
  conv_rhs => rw [as_sum P]
  rw [map_sum, Lsum_finset_sum, PI.WwEval.KM.applyAt0, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [peval_monomial, Lsum_monomial, eval_monomial, wt]
  ring

theorem peval_Gxz (x : Lt × ℕ × Fin N0 → ℂ_[l]) (nu : Lt → YoungDiagram)
    (I : PI.WwEval.KM.ColChoice N1 nu) :
    peval x (PI.WwEval.KM.Gxz N0 N1 nu I) =
      MvPolynomial.aeval (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
          MvPolynomial.C (x (v.1, v.2.1, a)) * MvPolynomial.X ((v.1, a, v.2.2) : Lt × Fin N0 × Fin N1))
        (PI.WwEval.KM.nablaX N1 nu I) := by
  unfold PI.WwEval.KM.Gxz PI.WwEval.KM.nablaX PI.WwEval.KM.minorXZ
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k
  simp [peval, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply]

theorem wwEval : PI.WwEval.WwEval := by
  intro Lt _ _ l _ N0 N1 nu Th x I
  rw [eval_applyAt0, peval_Gxz]
  simp only [Lsum, wt, mul_assoc]

end PI.WwEvalWork
