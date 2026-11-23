import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JBConjTranspose

noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate ContDiff Topology

namespace GlobalTheory.CompanionTheory.GelfAct

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have h : ∀ t : ℝ, (t : ℂ) • X = t • X := fun t => by ext; simp
  simp only [h]
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

def cf (π : G n →* (U →L[ℂ] U)) (w v : U) : Mat n → ℂ := fun g => ⟪w, piM π g v⟫_ℂ

def lin (π : G n →* (U →L[ℂ] U)) (w : U) (g : Mat n) : kfin π →ₗ[ℂ] ℂ :=
  ((innerSL ℂ w) ∘L (piM π g)).toLinearMap ∘ₗ (kfin π).subtype

def fam (π : G n →* (U →L[ℂ] U)) (D : Mat n → Module.End ℂ (kfin π)) (s : Bool) (a b : Fin n) : Module.End ℂ (kfin π) :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) + (if s then -Complex.I else Complex.I) • D (Matrix.single a b Complex.I))

end GlobalTheory.CompanionTheory.GelfAct

end
