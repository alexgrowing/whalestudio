import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_to_twisted_eigenfunction_support : ∀ {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W) (L : Subgroup G), IsCompact (L : Set G) → ∀ θ : L →* ℂˣ, IsOpen (θ.ker : Set L) → ∀ f : smoothPart (ind P τ), ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧ (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧ ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  first | exact @GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | exact GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | (intros; apply GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd <;> assumption)
