import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondPositionBijective
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspGAK

theorem cusp : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.GA.Cusp K := by
  intro K _ _ f _ hinv hY hY'
  exact cusp_of_constantTerms K f hinv hY hY'

end GlobalTheory.CompanionTheory.CuspGAK
