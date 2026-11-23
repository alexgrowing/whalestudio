import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SatisfiesGlRelationsBilinearLeft
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def pol (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin m) R →ₗ[R] MvPolynomial (Fin r × Fin m) R :=
  ∑ s : Fin m, (LinearMap.mulLeft R (X (a, s))) ∘ₗ
    ((pderiv (b, s) : Derivation R (MvPolynomial (Fin r × Fin m) R) (MvPolynomial (Fin r × Fin m) R)).toLinearMap)

theorem pol_apply (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    pol R a b f = ∑ s : Fin m, X (a, s) * pderiv (b, s) f := by
  simp [pol, LinearMap.sum_apply]

theorem pol_mul (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin m) R) :
    pol R a b (f * g) = pol R a b f * g + f * pol R a b g := by
  simp only [pol_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => by ring

theorem pol_X (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    pol R a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  classical
  rw [pol_apply]
  by_cases hv : v.1 = b
  · rw [if_pos hv, Finset.sum_eq_single v.2]
    · have : (b, v.2) = v := by rw [← hv]
      rw [this, pderiv_X_self, mul_one]
    · intro s _ hs
      rw [pderiv_X_of_ne, mul_zero]
      intro h; exact hs (by rw [h])
    · simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne, mul_zero]
    intro h; exact hv (by rw [h])

theorem pol_C (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (c : R) :
    pol R a b (C c : MvPolynomial (Fin r × Fin m) R) = 0 := by
  simp [pol_apply]

theorem rowGen_X' (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp [rowGen]

theorem deriv_rowGen (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (pol R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [pol_C, map_zero]
    have : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [this, Polynomial.derivative_C, mul_zero]
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, mul_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, mul_add, pol_mul, map_add, map_mul, map_mul, ← hp, pol_X]
    have hg : (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b (X v)) =
        rowGen R a b (if v.1 = b then X (a, v.2) else 0) := by
      rw [rowGen_X']
      by_cases hv : v.1 = b
      · simp only [hv, if_true, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
          Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_zero, add_zero, rowGen_X']
        by_cases hab : a = b
        · simp [hab]; ring
        · simp [hab]
      · simp [hv]
    rw [← hg]; ring

theorem rowGen_coeff_zero (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (rowGen R a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hh : ((Polynomial.aeval (0 : MvPolynomial (Fin r × Fin m) R)).restrictScalars R).comp (rowGen R a b) =
      AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowGen]
    split_ifs <;> simp
  have h2 := congrArg (fun φ => φ f) hh
  simpa [Polynomial.coe_aeval_eq_eval] using h2

theorem rowDiv_zero (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b 0 f = f := rowGen_coeff_zero R a b f

theorem rowDiv_succ (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b (k + 1) f * ((k : MvPolynomial (Fin r × Fin m) R) + 1) +
      (if a = b then rowDiv R a b k f * (k : MvPolynomial (Fin r × Fin m) R) else 0) =
      rowDiv R a b k (pol R a b f) := by
  have h := congrArg (fun p => Polynomial.coeff p k) (deriv_rowGen R a b f)
  unfold rowDiv
  rw [← h]
  by_cases hab : a = b
  · simp only [hab, if_true, add_mul, one_mul, Polynomial.coeff_add]
    rw [Polynomial.coeff_derivative]
    cases k with
    | zero => simp [Polynomial.coeff_derivative]
    | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast; ring
  · simp only [hab, if_false, one_mul, add_zero, Polynomial.coeff_derivative]

theorem pol_eq_rowDiv (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    pol R a b f = rowDiv R a b 1 f := by
  have h := rowDiv_succ R a b 0 f
  simp only [Nat.cast_zero, zero_add, mul_one, mul_zero, ite_self, add_zero, rowDiv_zero] at h
  exact h.symm

theorem pol_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {r m : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) :
    pol S a b (MvPolynomial.map ψ f) = MvPolynomial.map ψ (pol R a b f) := by
  simp [pol_apply, pderiv_map, map_sum]

theorem pol_mem_dualWeyl (R : Type) [CommRing R] {r m : ℕ} (ν : Fin m → ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) (hf : f ∈ dualWeyl R r m ν) : pol R a b f ∈ dualWeyl R r m ν := by
  rw [pol_eq_rowDiv]; exact dualWeylModuleRowDividedPowerStable R r m ν a b 1 f hf

theorem pol_eq_Eg {r m : ℕ} (a b : Fin r) :
    pol ℂ (m := m) a b = Formalism.REAL.Eg (fun _ => true) (fun _ => true) a b := by
  apply LinearMap.ext; intro f
  simp [pol_apply, Formalism.REAL.Eg, Formalism.REAL.bpl, Formalism.REAL.bop, Formalism.REAL.sgnv, LinearMap.sum_apply]

theorem pol_glRel (r m : ℕ) : Formalism.REAL.GlRel (fun a b : Fin r => (pol ℂ (m := m) a b : Module.End ℂ _)) := by
  have h := (Formalism.REAL.fockPairGl_of Formalism.REAL.canonicalCommutation_holds r m (fun _ => true) (fun _ => true)).1
  intro a b c d
  simp only [pol_eq_Eg]
  exact h a b c d

end PI.WGL
