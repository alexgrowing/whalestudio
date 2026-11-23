import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizationBasicOpenCover
import Mathlib
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalization_basicOpen_cover' : ∀ (U X : Scheme.{0}) (f : U ⟶ X), ∀ [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite), ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)), (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra; Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧ ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  first | exact @GlobalTheory.normalization_basicOpen_cover | exact GlobalTheory.normalization_basicOpen_cover | (intros; apply GlobalTheory.normalization_basicOpen_cover <;> assumption)
