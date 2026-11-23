import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CompactHarm

open MvPolynomial

theorem pd_comm {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, h]
    ring

theorem pd_X_mul {σ : Type*} [DecidableEq σ] (x u : σ) (Q : MvPolynomial σ ℂ) :
    pderiv x (X u * Q) = (if u = x then Q else 0) + X u * pderiv x Q := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : u = x
  · subst h; simp only [Pi.single_eq_same, mul_one, if_true]; ring
  · simp only [Pi.single_apply, h, if_false, mul_zero, add_zero, zero_add]

theorem dd_X_mul {σ : Type*} [DecidableEq σ] (x y u : σ) (R : MvPolynomial σ ℂ) :
    pderiv x (pderiv y (X u * R)) = (if u = y then pderiv x R else 0) + (if u = x then pderiv y R else 0) +
      X u * pderiv x (pderiv y R) := by
  rw [pd_X_mul, map_add, pd_X_mul]
  split_ifs <;> (try simp only [map_zero]) <;> ring

theorem gen {σ : Type*} [DecidableEq σ] {n : ℕ} (x y u w : Fin n → σ) (P : MvPolynomial σ ℂ)
    (hxy : ∑ j, pderiv (x j) (pderiv (y j) P) = 0)
    (hA1 : ∑ j, ∑ k, (if u k = y j then pderiv (x j) (pderiv (w k) P) else 0) = 0)
    (hA2 : ∑ j, ∑ k, (if u k = x j then pderiv (y j) (pderiv (w k) P) else 0) = 0) :
    ∑ j, pderiv (x j) (pderiv (y j) (∑ k, X (u k) * pderiv (w k) P)) = 0 := by
  simp only [map_sum, dd_X_mul]
  simp only [Finset.sum_add_distrib]
  rw [hA1, hA2, zero_add, zero_add, Finset.sum_comm]
  have : ∀ k, ∑ j, X (u k) * pderiv (x j) (pderiv (y j) (pderiv (w k) P)) = 0 := by
    intro k
    rw [← Finset.mul_sum]
    simp only [pd_comm (y _) (w k), pd_comm (x _) (w k)]
    rw [← map_sum, hxy, map_zero, mul_zero]
  simp [this]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_single {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      ∑ j, (raiO τ (fun _ : Fin n => true) ε' i j * lowO τ (fun _ : Fin n => true) ε' l j) Q +
        (if i = l then ((n : ℂ) / 2) • Q else 0) := by
  classical
  unfold fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_smul]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    intro l' _
    simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem low_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (hi : ε' i = false)
    (hl : ε' l = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      -∑ j, pderiv (τ, i, j) (pderiv (τ, l, j) Q) := by
  have hil : i ≠ l := fun e => by rw [e, hl] at hi; exact Bool.noConfusion hi
  rw [fockT_single, if_neg hil, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, hi, hl]

theorem up_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = true)
    (hb : ε' b = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      ∑ j, X (τ, a, j) * pderiv (τ, b, j) Q + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

theorem dn_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = false)
    (hb : ε' b = false) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      -∑ j, pderiv (τ, a, j) (X (τ, b, j) * Q) + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_compact_harm : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  classical
  intro D n m p P hP τ a b hab τ' i l hi hl
  have hL : ∀ (σ : D.what₂.Tau) (i l : Fin m), p σ ≤ (i : ℕ) → (l : ℕ) < p σ →
      ∑ j, pderiv (σ, i, j) (pderiv (σ, l, j) P) = 0 := by
    intro σ i l hi hl
    have := hP σ i l hi hl
    rw [low_eq σ _ i l (by simpa using hi) (by simpa using hl)] at this
    exact neg_eq_zero.1 this
  rw [low_eq τ' _ i l (by simpa using hi) (by simpa using hl), neg_eq_zero]
  let Lop : PolF D m n →ₗ[ℂ] PolF D m n :=
    ∑ j, (pderiv (τ', i, j)).toLinearMap ∘ₗ (pderiv (τ', l, j)).toLinearMap
  have hLop : ∀ Q, Lop Q = ∑ j, pderiv (τ', i, j) (pderiv (τ', l, j) Q) := by
    intro Q; simp [Lop, LinearMap.sum_apply]
  have hP0 : Lop P = 0 := by rw [hLop]; exact hL τ' i l hi hl
  have hite : ∀ (c : Prop) [Decidable c] (z : ℂ), Lop (if c then z • P else 0) = 0 := by
    intro c _ z; split_ifs <;> simp [hP0]
  rw [← hLop]
  by_cases ha : (a : ℕ) < p τ
  · have hb : (b : ℕ) < p τ := hab.1 ha
    rw [up_eq τ _ a b (by simpa using ha) (by simpa using hb), map_add, hite, add_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, a, k)) (fun k => (τ, b, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · by_cases h : τ = τ' ∧ a = l
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hL τ i b hi hb
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
  · have hb : ¬ (b : ℕ) < p τ := fun h => ha (hab.2 h)
    rw [dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]
    have e : ∑ k, pderiv (τ, a, k) (X (τ, b, k) * P) =
        (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) + ∑ k, X (τ, b, k) * pderiv (τ, a, k) P := by
      simp only [pd_X_mul, Finset.sum_add_distrib]
    have hS1 : Lop (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs <;> simp [hP0]
    rw [e, map_add, map_neg, map_add, hS1, zero_add, hite, add_zero, neg_eq_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, b, k)) (fun k => (τ, a, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
    · by_cases h : τ = τ' ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [pd_comm (τ, l, _) (τ, a, _)]
        exact hL τ a l (not_lt.1 ha) hl
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩

end GlobalTheory.CompactHarm
