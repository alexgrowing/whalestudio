import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBFiLower

noncomputable section
open Matrix Finset

namespace PI.EMR

def dg {m : ℕ} (e : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun j => (e j : ℂ))

def qf {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℂ) (e : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  B * dg e * Bᴴ

def ws {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℂ) (e : Fin m → ℝ) (k : Fin n) : ℝ :=
  ∑ j, ‖B k j‖ ^ 2 * e j

def ex {m : ℕ} (y : Fin m → ℝ) (t : ℝ) : Fin m → ℝ := fun j => Real.exp (t * y j)

def LeadRepr : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian → ∀ (i : ℕ) (hi : i ≤ N),
    ∃ (A : Matrix (Fin i) (Fin N) ℂ) (y : Fin N → ℝ), A * Aᴴ = 1 ∧
      Formalism.MainNotions.Ext.CutB.cBlead X i hi = qf A y ∧
      ∀ t : ℝ, Formalism.MainNotions.Ext.CutB.cBlead (NormedSpace.exp ((t : ℂ) • X)) i hi =
        qf A (ex y t)

def Rotate : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (e : Fin m → ℝ), A * Aᴴ = 1 →
    ∃ B : Matrix (Fin n) (Fin m) ℂ, B * Bᴴ = 1 ∧
      (∀ d : Fin m → ℝ, (qf B d).det = (qf A d).det ∧ (qf B d).trace = (qf A d).trace) ∧
      ∀ k l, k ≠ l → qf B e k l = 0

def Hadamard : Prop :=
  ∀ (n m : ℕ) (B : Matrix (Fin n) (Fin m) ℂ) (e : Fin m → ℝ), (∀ j, 0 < e j) →
    (qf B e).det.re ≤ ∏ k, ws B e k

def JensenExp : Prop :=
  ∀ (m : ℕ) (p y : Fin m → ℝ), (∀ j, 0 ≤ p j) → ∑ j, p j = 1 →
    Real.exp (∑ j, p j * y j) ≤ ∑ j, p j * Real.exp (y j)

def PowMean : Prop :=
  ∀ (m : ℕ) (p y : Fin m → ℝ), (∀ j, 0 ≤ p j) → ∑ j, p j = 1 → ∀ t : ℝ, 1 ≤ t →
    t * Real.log (∑ j, p j * Real.exp (y j)) ≤ Real.log (∑ j, p j * Real.exp (t * y j))

end PI.EMR
