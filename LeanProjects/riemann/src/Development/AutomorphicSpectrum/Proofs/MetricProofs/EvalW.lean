import Mathlib
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def nS (a : ℂ) (i : Fin 3) : ℝ := (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def wS (a : ℂ) : ℝ := ((1 + ‖a‖ ^ 2) ^ 2)⁻¹

def blk {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of fun p q : Fin (d + 1) =>
    Fin.cases (Fin.cases e (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => B p' q') q) p

def lin3 (n : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ := ∑ i, X i * C (n i)

def lin4 (n : Fin 3 → ℝ) : MvPolynomial (Option (Fin 3)) ℝ := rename some (lin3 n)

def rowW (u : Fin 2 → ℝ) (v : ℝ) : MvPolynomial (Option (Fin 2)) ℝ :=
  C (u 0) * X (some 0) + C (u 1) * X (some 1) + C v * X none

def evalW (n₀ n₁ : Fin 3 → ℝ) : MvPolynomial (Option (Fin 2)) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ :=
  aeval fun j => Option.elim j (X none) ![lin4 n₀, lin4 n₁]

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
