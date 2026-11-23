import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseVectorPairTwoPlaces
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_vector_pair_two_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.denseRange_ratPairs | exact GlobalTheory.CompanionTheory.SaGen.denseRange_ratPairs | (intros; apply GlobalTheory.CompanionTheory.SaGen.denseRange_ratPairs <;> assumption)
