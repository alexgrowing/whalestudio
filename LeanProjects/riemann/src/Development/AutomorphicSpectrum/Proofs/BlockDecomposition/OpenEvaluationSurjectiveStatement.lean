import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)),
  ∃ f : XS τ σ, (∀ x ∈ Cl k i t, evX f x = 0) ∧ eO ψ f = (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto <;> assumption)
