import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RareFlags

open Formalism.MainNotions.S GlobalTheory.Count

def FlagRare : Prop :=
  ∃ n₀ : ℕ, ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → n₀ ≤ B.I.n → q ^ 2 ≤ B.I.n →
    Real.log B.I.rd ≤ Real.exp B.I.n → Real.log B.I.f ≤ Real.sqrt B.I.n →
    prob B {x | least B.I x < 1 / 2} ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n))

example (q n : ℕ) : q ^ 2 ≤ n ↔ (q : ℝ) ≤ Real.sqrt n := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

example (I : AutInst) (x : I.GA) : least I x < 1 / 2 ↔ tau1 I x < 1 / 2 := by
  simp [tau1]

end GlobalTheory.IndefiniteRowSideFullHecke.RareFlags
