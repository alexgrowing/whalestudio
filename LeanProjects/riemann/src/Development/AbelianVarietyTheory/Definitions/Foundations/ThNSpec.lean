import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.CyclotomicQExpansion

open GlobalTheory.KZ GlobalTheory.Glue

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open Classical in

def thN (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n d : ℕ) (b : X.Fn l) : HahnSeries ℚ Ω :=
  if h : ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ ∧ IsLat 1 φ then
    h.choose else 0

theorem thN_spec (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n d : ℕ) (b : X.Fn l)
    (h : ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ ∧ IsLat 1 φ) :
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧ IsLat 1 (thN X A N l n d b) := by
  rw [thN, dif_pos h]
  exact h.choose_spec

end GlobalTheory.CyclotomicQExpansion
