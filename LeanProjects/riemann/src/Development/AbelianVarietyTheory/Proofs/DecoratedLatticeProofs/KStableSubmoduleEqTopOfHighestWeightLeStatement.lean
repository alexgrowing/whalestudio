import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KStableSubmoduleEqTopOfHighestWeightLe
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Formalism.FormalDegreeBessel.StatementIO
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N → (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  first | exact @GlobalTheory.HwSpan.eq_top_of_hwSub_le | exact GlobalTheory.HwSpan.eq_top_of_hwSub_le | (intros; apply GlobalTheory.HwSpan.eq_top_of_hwSub_le <;> assumption)
