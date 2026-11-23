import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_box_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | exact GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main <;> assumption)
