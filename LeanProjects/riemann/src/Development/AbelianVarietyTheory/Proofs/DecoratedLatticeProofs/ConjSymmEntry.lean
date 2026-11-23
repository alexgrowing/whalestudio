import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FreeN
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.Coords

theorem xPos_lt {κ τ j : ℕ} (a : XIx (Fin κ) (Fin τ) j) : xPos a < κ + j * (τ + 1) := by
  have e : j * (τ + 1) = j * τ + j := by ring
  rcases a with (i | i) | p
  · have := i.2; simp only [xPos]; omega
  · have := i.2; simp only [xPos]; omega
  · have h1 := p.1.2
    have h2 := p.2.2
    have h3 : (p.1.val + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ h1
    have h4 : (p.1.val + 1) * τ = p.1.val * τ + τ := by ring
    simp only [xPos]; omega

end GlobalTheory.SymBridge.Coords
