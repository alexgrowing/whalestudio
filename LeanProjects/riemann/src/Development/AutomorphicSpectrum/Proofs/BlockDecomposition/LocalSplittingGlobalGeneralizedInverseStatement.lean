import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingGlobalGeneralizedInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_splitting_global_generalized_inverse : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B), (∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) → ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal | exact GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_genInverse_of_forall_maximal <;> assumption)
