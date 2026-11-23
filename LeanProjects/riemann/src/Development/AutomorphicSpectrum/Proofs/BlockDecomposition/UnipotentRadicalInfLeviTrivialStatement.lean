import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivial
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_inf_levi_trivial : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM | exact GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM | (intros; apply GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM <;> assumption)
