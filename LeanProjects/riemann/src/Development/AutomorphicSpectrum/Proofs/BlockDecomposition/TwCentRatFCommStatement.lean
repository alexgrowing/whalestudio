import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFComm
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twCent_comm_of_charpoly_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable →
  ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  first | exact @GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | exact GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | (intros; apply GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm <;> assumption)
