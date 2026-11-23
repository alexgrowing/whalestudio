import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBFiLower

noncomputable section

open Finset

namespace PI.ExpMinorLowWork

open Formalism.MainNotions.Ext.CutB

def CBExp : Prop :=
  ∀ (i N : ℕ) (A : Matrix (Fin i) (Fin N) ℂ) (B : Matrix (Fin N) (Fin i) ℂ) (D : Fin i → Fin N → ℂ),
    (Matrix.of fun j k => ∑ m, A j m * D k m * B m k).det =
      ∑ f : Fin i → Fin N, (∏ k, D k (f k)) * ((∏ k, B (f k) k) * (A.submatrix id f).det)

def Det2 : Prop :=
  ∀ (n : ℕ) (k l : Fin n) (u v : Fin n → ℂ), k ≠ l →
    (Matrix.updateCol (Matrix.updateCol (1 : Matrix (Fin n) (Fin n) ℂ) k u) l v).det =
      u k * v l - u l * v k

def SpecExp : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian),
    NormedSpace.exp X = (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
      Matrix.diagonal (fun m => ((Real.exp (hX.eigenvalues m) : ℝ) : ℂ)) *
        star (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

def EigSum : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian),
    (∀ a b, ε a = ε b → X a b = 0) → ∀ S : Finset (Fin N),
      |∑ m ∈ S, hX.eigenvalues m| ≤
        Real.sqrt (2 * (min (cBp ε) (cBq ε) : ℕ)) * Real.sqrt (cBhs X) / 2

def RealStep : Prop :=
  ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (V ρ : ℝ), (∀ s, 0 ≤ w s) → ∑ s, w s = 1 →
    ∑ s, w s * y s = 0 → ∑ s, w s * y s ^ 2 = V → (∀ s, |y s| ≤ ρ / 2) → ρ ≤ 1 →
    (1 - ρ) / 2 * V ≤ Real.log (∑ s, w s * Real.exp (y s))

def Rep : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian), (∀ a, X a a = 0) →
    ∀ (i : ℕ) (hi : i ≤ N), ∃ w : Finset (Fin N) → ℝ, (∀ S, 0 ≤ w S) ∧ ∑ S, w S = 1 ∧
      ∑ S, w S * (∑ m ∈ S, hX.eigenvalues m) = 0 ∧
      ∑ S, w S * (∑ m ∈ S, hX.eigenvalues m) ^ 2 = cBV X i ∧
      (cBlead (NormedSpace.exp X) i hi).det =
        ((∑ S, w S * Real.exp (∑ m ∈ S, hX.eigenvalues m) : ℝ) : ℂ)

end PI.ExpMinorLowWork
