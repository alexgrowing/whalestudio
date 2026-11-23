import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues

noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix

def rectDiag (p q : ℕ) (f : ℕ → ℝ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then ((f i : ℝ) : ℂ) else 0

def diagP (p q : ℕ) (σ : ℕ → ℝ) : Mat p q :=
  Matrix.fromBlocks 0 (rectDiag p q σ) (rectDiag p q σ)ᴴ 0

def tanhDiag (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.diagonal fun a => (if a.isLeft then 1 else -1) *
    ((σ (posIx a) * Real.tanh (t * σ (posIx a)) : ℝ) : ℂ)

def hypMat (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.fromBlocks (Matrix.diagonal fun i : Fin p => ((Real.cosh (t * σ i) : ℝ) : ℂ))
    (rectDiag p q fun i => Real.sinh (t * σ i)) (rectDiag p q fun i => Real.sinh (t * σ i))ᴴ
    (Matrix.diagonal fun j : Fin q => ((Real.cosh (t * σ j) : ℝ) : ℂ))

def dil {p q : ℕ} (n : ℕ) (u : Ix p q → ℝ) : Pol p q n 0 →ₗ[ℂ] Pol p q n 0 :=
  ((Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) : ℝ) : ℂ) •
    (MvPolynomial.aeval fun l : Ln p q n 0 =>
      (MvPolynomial.C ((Real.exp (u l.1) : ℝ) : ℂ) * MvPolynomial.X l : Pol p q n 0)).toLinearMap

theorem diagonalElement_mem (p q : ℕ) (σ : ℕ → ℝ) : diagP p q σ ∈ pR p q := pY_mem (rectDiag p q σ)

theorem dil_monomial {p q n : ℕ} (u : Ix p q → ℝ) (α : Ln p q n 0 →₀ ℕ) (c : ℂ) :
    dil n u (MvPolynomial.monomial α c) =
      ((Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) : ℝ) : ℂ) • MvPolynomial.monomial α c := by
  have h : Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) =
      Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) * ∏ l : Ln p q n 0, Real.exp (u l.1) ^ α l := by
    simp only [← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add, Finset.sum_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h, Complex.ofReal_mul, mul_smul, dil, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.algebraMap_eq, Complex.ofReal_prod, Complex.ofReal_pow]
  ring

theorem dil_dil_neg {p q n : ℕ} (u : Ix p q → ℝ) (Φ : Pol p q n 0) : dil n u (dil n (-u) Φ) = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
  | monomial α c =>
    rw [dil_monomial, map_smul, dil_monomial, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      ← Finset.sum_add_distrib]
    simp

theorem dil_zero {p q n : ℕ} (Φ : Pol p q n 0) : dil n 0 Φ = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ]
  | monomial α c => rw [dil_monomial]; simp

end GlobalTheory.FockDecay
end
