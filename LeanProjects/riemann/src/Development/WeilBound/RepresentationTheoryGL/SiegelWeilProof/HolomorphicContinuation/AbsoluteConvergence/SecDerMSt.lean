import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerSt

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def mulR (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => ∑ i, y a i * A i j

def aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

def DMp (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  eulH H R - MvPolynomial.C (2 * (c : ℂ)) *
    (∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def CellM : Prop := ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian → ∀ f : ℝ → GR n,
  (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
  ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∃ (y₁ : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
    ∀ (p q : ℕ) (e : ℤ) (σ : ℝ), ∃ (mA w : GR n), IsUp mA ∧
      F0 p q e mA = Complex.exp (-((σ : ℂ) * ((p + q : ℕ) : ℂ) * H.trace)) ∧
      mR w = JJ n * nU (aE H (-σ) * b * aE H (-σ)) ∧ (aE H (-σ) * b * aE H (-σ)).IsHermitian ∧
      g * f σ = y₁ * mA * w

def CoV : Prop := ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.det ≠ 0 → ∀ F : (Fin m → Fin n → ℂ) → ℂ,
  ∫ x, F x = ((Complex.normSq A.det ^ m : ℝ) : ℂ) * ∫ y, F (mulR A y)

end PositivityTheory.Rg.Sw.AbsSt.SDM
