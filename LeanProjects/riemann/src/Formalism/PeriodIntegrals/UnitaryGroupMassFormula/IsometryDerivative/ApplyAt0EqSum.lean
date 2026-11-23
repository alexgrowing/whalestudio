import Mathlib
import Formalism.PeriodIntegrals.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm

open Finset

noncomputable section

namespace PI.IsoDerivBFintype

open PI.IsoDerivB

theorem le_of_oe {h n : ℕ} (J : Fin h ↪o Fin n) : h ≤ n := by
  simpa using Fintype.card_le_of_embedding J.toEmbedding

section lin

variable {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ)

def wt (α : Mono T N N') : ℂ := (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α

theorem applyAt0_eq_sum (P : MvPolynomial (Idx T N N') ℂ) (S : Finset (Mono T N N'))
    (hS : P.support ⊆ S) : applyAt0 P Θ = ∑ α ∈ S, MvPolynomial.coeff α P * wt Θ α := by
  have e : ∀ α, MvPolynomial.coeff α P * wt Θ α =
      MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α := fun α => by
    unfold wt; ring
  simp only [e]
  unfold applyAt0
  apply Finset.sum_subset hS
  intro α _ hα
  rw [MvPolynomial.notMem_support_iff.mp hα]
  ring

theorem applyAt0_add (P Q : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (P + Q) Θ = applyAt0 P Θ + applyAt0 Q Θ := by
  classical
  rw [applyAt0_eq_sum Θ (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    applyAt0_eq_sum Θ P (P.support ∪ Q.support) subset_union_left,
    applyAt0_eq_sum Θ Q (P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
  exact sum_congr rfl fun α _ => by rw [MvPolynomial.coeff_add]; ring

theorem applyAt0_zero : applyAt0 (0 : MvPolynomial (Idx T N N') ℂ) Θ = 0 := by
  simp [applyAt0]

theorem applyAt0_C_mul (c : ℂ) (P : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (MvPolynomial.C c * P) Θ = c * applyAt0 P Θ := by
  classical
  rw [applyAt0_eq_sum Θ (MvPolynomial.C c * P) P.support ?_,
    applyAt0_eq_sum Θ P P.support subset_rfl, mul_sum]
  · exact sum_congr rfl fun α _ => by rw [MvPolynomial.coeff_C_mul]; ring
  · intro α hα
    rw [MvPolynomial.mem_support_iff] at hα ⊢
    rw [MvPolynomial.coeff_C_mul] at hα
    exact right_ne_zero_of_mul hα

theorem applyAt0_mul_C (c : ℂ) (P : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (P * MvPolynomial.C c) Θ = applyAt0 P Θ * c := by
  rw [mul_comm, applyAt0_C_mul, mul_comm]

theorem applyAt0_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (∑ i ∈ s, P i) Θ = ∑ i ∈ s, applyAt0 (P i) Θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, applyAt0_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, applyAt0_add, ih]

end lin

section main

variable {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
  (nu : Lt → YoungDiagram)

instance fintypeCC (n : ℕ) : Fintype (ColChoice (Lt := Lt) n nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin n))

def mY (J : ColChoice N nu) : MvPolynomial (FrV T N) ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu z).colLen c) =>
    if h : (j : ℕ) < N then (MvPolynomial.X (tp z, J z c i, ⟨j, h⟩) : MvPolynomial (FrV T N) ℂ)
    else 0)

theorem eval_mY (J : ColChoice N nu) (y : T → Matrix (Fin N) (Fin N) ℂ) :
    MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) (mY tp nu J) = minY N nu J (frC tp y) := by
  unfold mY minY
  rw [map_prod]
  refine prod_congr rfl fun z _ => ?_
  rw [map_prod]
  refine prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, frC, colsOf]
  split_ifs <;> simp

variable [Fintype T]

theorem Q_eq (φ : LaC N nu) (Q : MvPolynomial (FrV T N) ℂ)
    (hQ : ∀ y, evFr Q y = canC φ (frC tp y)) :
    Q = ∑ J, MvPolynomial.C (φ J) * mY tp nu J := by
  apply MvPolynomial.funext
  intro x
  let y : T → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b => x (τ, a, b)
  have h1 : evFr Q y = MvPolynomial.eval x Q := rfl
  have h2 : ∀ J, MvPolynomial.eval x (mY tp nu J) = minY N nu J (frC tp y) := fun J =>
    eval_mY tp nu J y
  rw [← h1, hQ, map_sum]
  simp only [map_mul, MvPolynomial.eval_C, h2]
  unfold canC prC hvC
  rw [finsum_eq_sum_of_fintype]

end main

end PI.IsoDerivBFintype
