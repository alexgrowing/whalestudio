import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquationsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscPairDer

open MvPolynomial

variable {P Q : ℕ}

def derForm (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ) (T : MvPolynomial (Ix P Q) ℂ → ℂ)
    (f : MvPolynomial (Ix P Q) ℂ) : ℂ :=
  ∑ i, ∑ j, A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)) + ∑ l, x' l * T (pderiv l f)

theorem derForm_comb {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T U : MvPolynomial (Ix P Q) ℂ → ℂ) (a : ℂ) (b : κ → ℂ) (e : κ → Ix P Q)
    (hU : ∀ g, U g = a * T g + ∑ k, b k * T (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' U f = a * derForm A' x' T f + ∑ k, b k * derForm A' x' T (pderiv (e k) f) := by
  simp only [derForm, hU, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∑ i, ∑ j, ∑ k, A' i j * (b k * T (pderiv (e k) (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)))) =
      ∑ k, ∑ i, ∑ j, b k * (A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) (pderiv (e k) f)))) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset κ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  have h2 : ∑ l, ∑ k, x' l * (b k * T (pderiv (e k) (pderiv l f))) =
      ∑ k, ∑ l, b k * (x' l * T (pderiv l (pderiv (e k) f))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  rw [h1, h2]
  simp only [mul_left_comm a]
  ring

theorem pderiv_X_mul (m l : Ix P Q) (f : MvPolynomial (Ix P Q) ℂ) :
    pderiv m (X l * f) = X l * pderiv m f + if m = l then f else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  by_cases h : m = l
  · simp [h]
  · simp [h, Ne.symm h]

theorem derForm_X_inl (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inl i) * f) = derForm A' x' (fun g => T (X (Sum.inl i) * g)) f +
      (x' (Sum.inl i) * T f + ∑ j, A' i j * T (pderiv (Sum.inr j) f)) := by
  simp only [derForm, pderiv_X_mul, map_add, apply_ite T, map_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inl.injEq]
  rw [Finset.sum_comm (f := fun i' j => if i' = i then A' i' j * T (pderiv (Sum.inr j) f) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem derForm_X_inr (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inr j) * f) = derForm A' x' (fun g => T (X (Sum.inr j) * g)) f +
      (x' (Sum.inr j) * T f + ∑ i, A' i j * T (pderiv (Sum.inl i) f)) := by
  simp only [derForm, pderiv_X_mul, map_add, apply_ite T, apply_ite (pderiv _), map_zero, mul_add,
    Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inr.injEq]
  ring

def pair (F : Fock (Ix P Q)) (v : F.H) : MvPolynomial (Ix P Q) ℂ →+ ℂ where
  toFun f := inner ℂ (F.ι f) v
  map_zero' := by simp
  map_add' f g := by simp [inner_add_left]

theorem step {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : ℝ → MvPolynomial (Ix P Q) ℂ → ℂ) (l : Ix P Q) (a : ℝ → ℂ) (b : ℝ → κ → ℂ) (a' : ℂ) (b' : κ → ℂ)
    (e : κ → Ix P Q) (ha : HasDerivAt a a' 0) (hb : ∀ k, HasDerivAt (fun t => b t k) (b' k) 0)
    (hU : ∀ t g, T t (X l * g) = a t * T t g + ∑ k, b t k * T t (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ)
    (h0 : HasDerivAt (fun t => T t f) (derForm A' x' (T 0) f) 0)
    (h1 : ∀ m, HasDerivAt (fun t => T t (pderiv m f)) (derForm A' x' (T 0) (pderiv m f)) 0) :
    HasDerivAt (fun t => T t (X l * f)) (derForm A' x' (fun g => T 0 (X l * g)) f +
      (a' * T 0 f + ∑ k, b' k * T 0 (pderiv (e k) f))) 0 := by
  rw [derForm_comb A' x' (T 0) _ (a 0) (b 0) e (hU 0)]
  simp only [hU]
  refine ((ha.fun_mul h0).fun_add (HasDerivAt.fun_sum (u := Finset.univ)
    fun k _ => (hb k).fun_mul (h1 (e k)))).congr_deriv ?_
  rw [Finset.sum_add_distrib]
  ring

theorem hasDerivAt_inner_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  intro P Q F A x v A' x' hv hA hx f
  change HasDerivAt (fun t => pair F (v t) f) (derForm A' x' (pair F (v 0)) f) 0
  have key : ∀ (N : ℕ) (α : Ix P Q →₀ ℕ), α.degree ≤ N → ∀ c : ℂ,
      HasDerivAt (fun t => pair F (v t) (monomial α c)) (derForm A' x' (pair F (v 0)) (monomial α c)) 0 := by
    have h0 : ∀ c : ℂ, HasDerivAt (fun t => pair F (v t) (monomial 0 c))
        (derForm A' x' (pair F (v 0)) (monomial 0 c)) 0 := fun c => by
      have e : ∀ t, pair F (v t) (monomial 0 c) = (starRingEnd ℂ) c := fun t => by
        have e1 : (monomial 0 c : MvPolynomial (Ix P Q) ℂ) = c • monomial 0 1 := by
          rw [smul_monomial, smul_eq_mul, mul_one]
        change inner ℂ (F.ι (monomial 0 c)) (v t) = _
        rw [e1, map_smul, inner_smul_left, hv t 0]
        simp [expPS, MvPowerSeries.coeff_apply]
      simp only [e]
      refine (hasDerivAt_const _ _).congr_deriv ?_
      simp [derForm]
    intro N
    induction N with
    | zero =>
      intro α hα c
      obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (Nat.le_zero.1 hα)
      exact h0 c
    | succ N ih =>
      intro α hα c
      by_cases hz : α = 0
      · subst hz; exact h0 c
      obtain ⟨l, hl⟩ : ∃ l, α l ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hz (Finsupp.ext hh)
      obtain ⟨β, rfl⟩ : ∃ β, α = Finsupp.single l 1 + β :=
        exists_add_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero hl))
      have hβ : β.degree ≤ N := by
        rw [map_add, Finsupp.degree_single] at hα
        omega
      have e : (monomial (Finsupp.single l 1 + β) c : MvPolynomial (Ix P Q) ℂ) = X l * monomial β c := by
        rw [X, monomial_mul, one_mul]
      have h1 : ∀ m, HasDerivAt (fun t => pair F (v t) (pderiv m (monomial β c)))
          (derForm A' x' (pair F (v 0)) (pderiv m (monomial β c))) 0 := fun m => by
        rw [pderiv_monomial]
        exact ih _ ((Finsupp.degree_mono tsub_le_self).trans hβ) _
      rw [e]
      rcases l with i | j
      · rw [derForm_X_inl]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inl i)) (fun t j => A t i j) _ _ Sum.inr
          (hx _) (hA i) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).1 i) _ (ih _ hβ c) h1
      · rw [derForm_X_inr]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inr j)) (fun t i => A t i j) _ _ Sum.inl
          (hx _) (fun i => hA i j) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).2 j) _ (ih _ hβ c) h1
  induction f using MvPolynomial.induction_on' with
  | monomial α c => exact key _ α le_rfl c
  | add f g hf hg =>
    simp only [map_add]
    refine (hf.fun_add hg).congr_deriv ?_
    simp only [derForm, map_add, mul_add, Finset.sum_add_distrib]
    ring

end GlobalTheory.OscPairDer

end
