import Mathlib
import Formalism.DegreeFormula.FlagDegFormula

noncomputable section
open MvPolynomial Finset

namespace GlobalTheory.FlagHook

def altCoeff {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (-1) ^ Formalism.DegreeFormula.dimFl ι N * ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
    P.coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => n x.1 (σ x.1 x.2)))

def rho (N : ℕ) : Fin N → ℕ := fun c => N - 1 - (c : ℕ)

def hookRho (N k r : ℕ) : Fin N → ℕ :=
  fun c => N - 1 - (c : ℕ) + (if (c : ℕ) = 0 then k - r else if (c : ℕ) ≤ r then 1 else 0)

def detE {N : ℕ} (n : Fin N → ℕ) : MvPolynomial (Fin N) ℝ :=
  Matrix.det (Matrix.of fun i c : Fin N => C (((n c).factorial : ℝ)⁻¹) * X i ^ n c)

def hookR (N k : ℕ) : MvPolynomial (Fin N) ℝ :=
  ∑ r ∈ range k, C ((-1 : ℝ) ^ r) * detE (hookRho N k r)

def hookFl {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ r ∈ range k, (-1 : ℝ) ^ r *
    altCoeff (fun τ' => if τ' = τ then hookRho N k r else rho N) P

def pw {ι : Type} (N : ℕ) (τ : ι) (k : ℕ) : MvPolynomial (ι × Fin N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def kap {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (u : ι → Fin N → ℝ) (k : ℕ)
    (γ Q : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  k * Formalism.DegreeFormula.degFl ι N (γ * Q) / (((Formalism.DegreeFormula.dimFl ι N : ℝ) + 1) * Formalism.DegreeFormula.flagDeg ι N u)

def IsDecomp {ι : Type} [Fintype ι] {N : ℕ} (u : ι → Fin N → ℝ)
    (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ) : Prop :=
  (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (Formalism.DegreeFormula.dimFl ι N + 1 - k)) ∧
    Formalism.DegreeFormula.linRoot u ^ (Formalism.DegreeFormula.dimFl ι N + 1) = ∑ τ, ∑ k ∈ Icc 1 N, pw N τ k * Q τ k

theorem altCoeff_rho {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (fun _ => rho N) P = Formalism.DegreeFormula.degFl ι N P := rfl

end GlobalTheory.FlagHook
