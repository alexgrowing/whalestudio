import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilWhittakerLeftUnipotent
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WeilSplit.SplitAdditiveCharacter

theorem sPsi : Ad3.K.GL2LocalData.SPsi := by
  intro F _ _ _ _ _ _ _ χ _ _ c₁ c₂ Φ x g
  exact GlobalTheory.CompanionTheory.WeilSplit.Uni.split_weil_whittaker_unipotent_equivariant F χ c₁ c₂ Φ x g

end GlobalTheory.CompanionTheory.WeilSplit.SplitAdditiveCharacter
