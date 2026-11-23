import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.BranchFormula

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {N n : ℕ}

def BrEqv (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N)
    (sg : ι → DomWeight n) (T : (Frames G → ℂ) →ₗ[ℂ] (Frames G' → ℂ)) : Prop :=
  (∀ Φ ∈ ValC G lam, T Φ ∈ ValC G' sg) ∧
    ∀ (k : ι → Matrix (Fin n) (Fin n) ℂ) (kt : ι → Matrix (Fin N) (Fin N) ℂ), IsUni k → (∀ τ, IsBlock hN (kt τ) (k τ) 1) →
      ∀ Φ ∈ ValC G lam, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr kt y y' → Φ' y = Φ y') →
        ∀ z z', IsTr k z z' → T Φ' z = T Φ z'

example (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N)
    (sg : ι → DomWeight n) : BrEqv hN G G' lam sg 0 :=
  ⟨fun _ _ => Submodule.zero_mem _, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

end GlobalTheory.KJInf

end
