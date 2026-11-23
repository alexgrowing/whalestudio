import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDiagonalTwoPlaces
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_diagonal_two_places : ∀ {F : Type} [Field F] [NumberField F] {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂] [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}, IsPlacesIdem A₁ A₂ (P₁.inj 1) → IsPlacesIdem B₁ B₂ (P₂.inj 1) → Disjoint A₁ B₁ → Disjoint A₂ B₂ → DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.DensePair.denseRange_pair | exact GlobalTheory.CompanionTheory.SaGen.DensePair.denseRange_pair | (intros; apply GlobalTheory.CompanionTheory.SaGen.DensePair.denseRange_pair <;> assumption)
