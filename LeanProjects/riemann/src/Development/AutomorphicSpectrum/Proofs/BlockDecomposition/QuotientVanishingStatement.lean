import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientVanishing
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_vanishing : GlobalTheory.CompanionTheory.LocVan.QuotVanish := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.quotVanish | exact GlobalTheory.CompanionTheory.LocVan.quotVanish | (intros; apply GlobalTheory.CompanionTheory.LocVan.quotVanish <;> assumption)
