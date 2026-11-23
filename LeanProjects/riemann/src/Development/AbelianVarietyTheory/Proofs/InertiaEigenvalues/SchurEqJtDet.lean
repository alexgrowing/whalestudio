import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie

noncomputable section

namespace GlobalTheory.JSW

def padTo {m n : ℕ} (_h : m ≤ n) (l : Fin m → ℕ) : Fin n → ℕ :=
  fun i => if hi : (i : ℕ) < m then l ⟨i, hi⟩ else 0

open Classical in

def antiParts (m d : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.Nat.antidiagonalTuple m d).filter Antitone

def jtDet {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) : A :=
  Matrix.det (Matrix.of fun i j : Fin m =>
    if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat))

def staircase (m : ℕ) : Fin m → ℕ := fun i => m - 1 - i

def alternant (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) : MvPolynomial (Fin m) A :=
  Matrix.det (Matrix.of fun i j : Fin m => (MvPolynomial.X j : MvPolynomial (Fin m) A) ^ μ i)

theorem schur_eq_jtDet (n : ℕ) (l : Fin n → ℕ) :
    schur n l = jtDet n (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := rfl

theorem mem_antiParts {m d : ℕ} {l : Fin m → ℕ} : l ∈ antiParts m d ↔ ∑ i, l i = d ∧ Antitone l := by
  classical
  simp [antiParts, Finset.Nat.mem_antidiagonalTuple]

theorem padTo_self {m : ℕ} (l : Fin m → ℕ) : padTo le_rfl l = l := by
  funext i; simp [padTo, i.2]

example : alternant ℤ 2 (staircase 2) = MvPolynomial.X 0 - MvPolynomial.X 1 := by
  simp [alternant, staircase, Matrix.det_fin_two]

example : (antiParts 2 2).card = 2 := by decide

end GlobalTheory.JSW
