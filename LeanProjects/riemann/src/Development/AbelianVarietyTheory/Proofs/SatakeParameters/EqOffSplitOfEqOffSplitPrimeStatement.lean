import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffSplitOfEqOffSplitPrime
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqOffSplit_of_eqOff_splitPrime : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  first | exact @GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff | exact GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff | (intros; apply GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff <;> assumption)
