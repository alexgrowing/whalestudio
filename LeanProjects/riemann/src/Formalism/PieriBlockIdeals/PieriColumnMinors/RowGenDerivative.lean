import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQWordAdj
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

def der (r n : ℕ) (a b : Fin r) :
    Derivation ℚ (MvPolynomial (Fin r × Fin n) ℚ) (MvPolynomial (Fin r × Fin n) ℚ) :=
  mkDerivation ℚ fun v => if v.1 = b then X (a, v.2) else 0

theorem der_X {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    der r n a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  rw [der, mkDerivation_X]

theorem der_comm {r n : ℕ} (a b c d : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    der r n a b (der r n c d f) - der r n c d (der r n a b f) =
      (if b = c then der r n a d f else 0) - (if d = a then der r n c b f else 0) := by
  have h : ⁅der r n a b, der r n c d⁆ =
      (if b = c then der r n a d else 0) - (if d = a then der r n c b else 0) := by
    apply MvPolynomial.derivation_ext
    rintro ⟨x, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    have e3 : ∀ (P : Prop) [Decidable P]
        (D : Derivation ℚ (MvPolynomial (Fin r × Fin n) ℚ) (MvPolynomial (Fin r × Fin n) ℚ))
        (g : MvPolynomial (Fin r × Fin n) ℚ), (if P then D else 0) g = if P then D g else 0 := by
      intro P _ D g
      split_ifs <;> simp
    simp only [e3, der_X]
    by_cases h1 : x = d
    · subst h1
      by_cases h2 : x = b
      · subst h2
        by_cases h3 : x = c
        · subst h3
          by_cases h4 : x = a
          · subst h4; simp [der_X]
          · have h4' : ¬ a = x := fun h => h4 h.symm
            simp [der_X, h4, h4']
        · have h3' : ¬ c = x := fun h => h3 h.symm
          by_cases h4 : x = a
          · subst h4; simp [der_X, h3, h3']
          · have h4' : ¬ a = x := fun h => h4 h.symm
            simp [der_X, h3, h4, h3', h4']
      · by_cases h3 : b = c
        · subst h3; simp [der_X, h2]
        · have h3' : ¬ c = b := fun h => h3 h.symm
          simp [der_X, h2, h3, h3']
    · by_cases h2 : x = b
      · subst h2
        by_cases h4 : d = a
        · subst h4; simp [der_X, h1]
        · have h4' : ¬ a = d := fun h => h4 h.symm
          simp [der_X, h1, h4, h4']
      · simp [der_X, h1, h2]
  have h' := congrArg (fun D => D f) h
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at h'
  rw [h']
  split_ifs <;> simp

theorem rowGen_X' {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen ℚ a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  rw [rowGen, aeval_X]

theorem rowGen_C' {r n : ℕ} (a b : Fin r) (c : ℚ) :
    rowGen ℚ a b (C c : MvPolynomial (Fin r × Fin n) ℚ) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem rowGen_derivative {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    (1 + if a = b then Polynomial.X else 0) * Polynomial.derivative (rowGen ℚ a b f) =
      rowGen ℚ a b (der r n a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen_C', ← MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, mul_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      ← hp, der_X, rowGen_X']
    by_cases h1 : v.1 = b
    · by_cases h2 : a = b
      · subst h2
        have e : ((a, v.2) : Fin r × Fin n) = v := by rw [← h1]
        simp only [h1, if_true, rowGen_X', e]
        simp
        ring
      · have h3 : ¬ ((a, v.2) : Fin r × Fin n).1 = b := h2
        simp only [h1, h2, if_true, if_false, rowGen_X', h3]
        simp
        ring
    · simp only [h1, if_false, map_zero]
      simp
      ring

theorem rowDiv_zero' {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) : rowDiv ℚ a b 0 f = f := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen_C']
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, rowGen_X']
    split_ifs <;> simp

theorem rowDiv_succ {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) f =
      rowDiv ℚ a b k (der r n a b f) - (if a = b then (k : ℚ) • rowDiv ℚ a b k f else 0) := by
  have h := congrArg (fun P => Polynomial.coeff P k) (rowGen_derivative a b f)
  beta_reduce at h
  unfold rowDiv
  rw [← h, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_derivative]
  by_cases hab : a = b
  · simp only [hab, if_true]
    cases k with
    | zero => simp [MvPolynomial.smul_eq_C_mul, mul_comm]
    | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      simp only [MvPolynomial.smul_eq_C_mul]
      push_cast
      simp only [map_add, map_natCast, map_one]
      ring
  · simp only [hab, if_false, zero_mul, Polynomial.coeff_zero, add_zero, sub_zero, MvPolynomial.smul_eq_C_mul]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

theorem rowDiv_one {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    rowDiv ℚ a b 1 f = der r n a b f := by
  have h := rowDiv_succ a b 0 f
  simpa [rowDiv_zero'] using h

theorem closed_of_der {r n : ℕ} (a b : Fin r) (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : ∀ f ∈ M, der r n a b f ∈ M) (k : ℕ) : ∀ f ∈ M, rowDiv ℚ a b k f ∈ M := by
  induction k with
  | zero => intro f hf; rwa [rowDiv_zero']
  | succ k ih =>
    intro f hf
    have h := rowDiv_succ a b k f
    have h2 : rowDiv ℚ a b k (der r n a b f) - (if a = b then (k : ℚ) • rowDiv ℚ a b k f else 0) ∈ M := by
      refine M.sub_mem (ih _ (hM f hf)) ?_
      split_ifs
      · exact M.smul_mem _ (ih f hf)
      · exact M.zero_mem
    rw [← h] at h2
    have h3 := M.smul_mem (((k + 1 : ℕ) : ℚ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h3

theorem der_pow {r n : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    rowDiv ℚ a b k f = ((k.factorial : ℚ)⁻¹) • ((der r n a b : Module.End ℚ _) ^ k) f := by
  induction k generalizing f with
  | zero => simp [rowDiv_zero']
  | succ k ih =>
    have h := rowDiv_succ a b k f
    simp only [hab, if_false, sub_zero] at h
    rw [ih] at h
    have h3 := congrArg (fun x => (((k + 1 : ℕ) : ℚ)⁻¹) • x) h
    beta_reduce at h3
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h3
    rw [h3, smul_smul, pow_succ, Module.End.mul_apply, Nat.factorial_succ]
    congr 1
    push_cast
    rw [mul_inv]

theorem der_mem {r n : ℕ} (ν : Fin n → ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (hf : f ∈ dualWeyl ℚ r n ν) : (der r n a b : Module.End ℚ _) f ∈ dualWeyl ℚ r n ν := by
  have h := rowDivStable ℚ r n ν a b 1 f hf
  rwa [rowDiv_one] at h

theorem fock_add_left {σ : Type} (f f' g : MvPolynomial σ ℚ) : fockQ (f + f') g = fockQ f g + fockQ f' g :=
  (fockQBilin σ f f' g 0).1

theorem fock_smul_left {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ (c • f) g = c * fockQ f g :=
  (fockQBilin σ f 0 g c).2

theorem fock_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := (fockQPos σ f g).1

theorem fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [fock_symm, fock_add_left, fock_symm g, fock_symm g']

theorem fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [fock_symm, fock_smul_left, fock_symm g]

theorem fock_der {r n : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin n) ℚ) :
    fockQ (der r n a b f) g = fockQ f (der r n b a g) := by
  rw [← rowDiv_one, ← rowDiv_one]
  exact fockQRowDivAdj r n a b 1 f g

end Formalism.CohomologicalDescent.LR
