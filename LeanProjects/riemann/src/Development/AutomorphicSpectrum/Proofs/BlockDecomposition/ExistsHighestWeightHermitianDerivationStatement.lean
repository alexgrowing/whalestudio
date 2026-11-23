import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivation
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_hermitian_derivation : ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν → ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L)) (K : Fin n → Fin n → Module.End ℂ L) (v : L), Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧ IsDerivK σ K ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧ (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧ ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ L (σ k) = weylChar ν z := by
  first | exact @GlobalTheory.CompanionTheory.RmModel.rmModel | exact GlobalTheory.CompanionTheory.RmModel.rmModel | (intros; apply GlobalTheory.CompanionTheory.RmModel.rmModel <;> assumption)
