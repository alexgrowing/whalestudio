import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameters_ok_of_laws : ∀ (D : D7) (J : CoreJ D) (T : Top D) (EX : ErrX D) (p : ℕ), LawsJ J → LawsP T → LawsSh T → T.toCore = J.toCore → T.Q.Canon → FieldOK0 D p → HalfEX T.toCore EX → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1 ∧ (T.dδ j n).pd = p) → ∀ j, InR D j → ParOK T EX p j := by
  first | exact @GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws | exact GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws | (intros; apply GlobalTheory.FinalJoin2.liftIndexParameterConditions_of_coreAndShortLaws <;> assumption)
