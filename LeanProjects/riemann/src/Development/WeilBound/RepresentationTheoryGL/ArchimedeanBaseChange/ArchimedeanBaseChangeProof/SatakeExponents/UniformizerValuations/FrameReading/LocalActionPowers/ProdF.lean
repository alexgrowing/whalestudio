import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpParabEqLevOpCt

noncomputable section

open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.F.FA.Abs

variable {Γ ι : Type} [Group Γ] [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)]

def prodF (p : ∀ i, Γ →* M i) (φ : ∀ i, M i → ℂ) (x : Γ) : ℂ := ∏ᶠ j, φ j (p j x)

def iter (e : ∀ i, M i →* Γ) (KH : ∀ i, Subgroup (M i)) (φ : ∀ i, M i → ℂ) (Ψ : Γ → ℂ) : List ι → Γ → ℂ
  | [] => Ψ
  | i :: l => fun y => hint (KH i) fun m => φ i m * iter e KH φ Ψ l (y * e i m)

def kerD (p : ∀ i, Γ →* M i) (D : Set ι) : Subgroup Γ := ⨅ j ∈ D, (p j).ker

end PositivityTheory.Rg.BcB.F.FA.Abs

end
