import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      (∏ s, (t s : ℂ) ^ (Finsupp.weight (colW n' n) d s)) • monomial d c := by
  have hX : ∀ v : Fin n' × Fin n, matRep n n' (diagGL ℂ n t, 1) (X v) = (t v.2 : ℂ) • X v := by
    rintro ⟨a, s⟩
    rw [matRep_X, Finset.sum_eq_single a, Finset.sum_eq_single s]
    · simp [diagGL, smul_eq_C_mul]
    · intro b _ hb
      simp [diagGL, hb]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  induction d using Finsupp.induction_linear generalizing c with
  | zero => simp [matRep_apply]
  | add d e hd he =>
    have h1 : (monomial (d + e) c : MvPolynomial (Fin n' × Fin n) ℂ) = monomial d c * monomial e 1 := by
      rw [monomial_mul, mul_one]
    have hd' := hd c
    have he' := he 1
    rw [matRep_apply] at hd' he'
    rw [h1, matRep_apply, map_mul, hd', he', smul_mul_smul_comm, ← Finset.prod_mul_distrib]
    simp only [map_add, Pi.add_apply, pow_add]
  | single v k =>
    have h1 := hX v
    rw [matRep_apply] at h1
    rw [← C_mul_X_pow_eq_monomial, matRep_apply, map_mul, map_pow, h1, smul_pow, mul_smul_comm]
    congr 1
    · rw [Finset.prod_eq_single v.2]
      · simp [Finsupp.weight_single, colW]
      · intro b _ hb
        simp [Finsupp.weight_single, colW, hb]
      · simp
    · simp

theorem matRep_diagGL_component {n n' : ℕ} (t : Fin n → ℂˣ) (μ : Fin n → ℕ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (weightedHomogeneousComponent (colW n' n) μ v) =
      (∏ s, (t s : ℂ) ^ μ s) • weightedHomogeneousComponent (colW n' n) μ v := by
  classical
  rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [matRep_diagGL_monomial, (Finset.mem_filter.1 hd).2]

noncomputable def torusPowChar {n : ℕ} (μ : Fin n → ℕ) : (Fin n → ℂˣ) →* ℂ where
  toFun t := ∏ s, (t s : ℂ) ^ μ s
  map_one' := by simp
  map_mul' a b := by simp [mul_pow, Finset.prod_mul_distrib]

theorem torusPowChar_injective {n : ℕ} : Function.Injective (torusPowChar (n := n)) := by
  classical
  intro μ ν h
  funext a
  let t : Fin n → ℂˣ := Pi.mulSingle a (Units.mk0 2 two_ne_zero)
  have hprod : ∀ e : Fin n → ℕ, torusPowChar e t = 2 ^ e a := by
    intro e
    change ∏ s, (t s : ℂ) ^ e s = _
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb
      simp [t, hb]
    · simp
  have h1 : (2 : ℂ) ^ μ a = 2 ^ ν a := by rw [← hprod, ← hprod, h]
  have h' : (2 : ℕ) ^ μ a = 2 ^ ν a := by exact_mod_cast h1
  exact Nat.pow_right_injective le_rfl h'

theorem weightedHomogeneousComponent_colW_mem (n n' : ℕ) (M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ))
    (hM : ∀ t : Fin n → ℂˣ, ∀ v ∈ M, matRep n n' (diagGL ℂ n t, 1) v ∈ M) (ν : Fin n → ℕ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) (hv : v ∈ M) :
    weightedHomogeneousComponent (colW n' n) ν v ∈ M := by
  classical
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  have hfin := weightedHomogeneousComponent_finsupp (w := colW n' n) v
  have hsum := sum_weightedHomogeneousComponent (colW n' n) v
  rw [finsum_eq_sum _ hfin] at hsum
  by_cases hν : ν ∈ hfin.toFinset
  · have hli := (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ (torusPowChar_injective (n := n))
    refine linearIndependent_iff'.1 hli hfin.toFinset
      (fun μ => l (weightedHomogeneousComponent (colW n' n) μ v)) ?_ ν hν
    funext t
    have h0 := (Submodule.mem_dualAnnihilator l).1 hl _ (hM t v hv)
    rw [← hsum, map_sum, map_sum] at h0
    rw [Finset.sum_apply, Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [matRep_diagGL_component, map_smul, smul_eq_mul, mul_comm]
    rfl
  · have : weightedHomogeneousComponent (colW n' n) ν v = 0 := by
      by_contra h
      exact hν (hfin.mem_toFinset.2 h)
    rw [this, map_zero]

end GlobalTheory.GLDuality
