import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FinitePresentationOfFaithfullyFlat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePresentation_of_faithfully_flat : ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D → Module.FaithfullyFlat C D → Algebra.FinitePresentation R D → Algebra.FinitePresentation R C := by
  first | exact @GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat | exact GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat | (intros; apply GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat <;> assumption)
