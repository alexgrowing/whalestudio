import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

namespace GlobalTheory.LocAsm

def exOne {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) : ∀ b, X b → ℂ := fun b x =>
  match b, x with
  | .ex _ _, _ => 1
  | .theta i j, x => φ (.theta i j) x

@[simp] theorem exOne_ex {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.ex i j)) :
    exOne φ (.ex i j) x = 1 := rfl

@[simp] theorem exOne_theta {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.theta i j)) :
    exOne φ (.theta i j) x = φ (.theta i j) x := rfl

end GlobalTheory.LocAsm
