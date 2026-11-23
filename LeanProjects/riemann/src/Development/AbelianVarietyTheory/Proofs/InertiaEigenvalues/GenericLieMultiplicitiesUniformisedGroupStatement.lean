import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_lie_multiplicities_uniformised_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (IsLocalRing.maximalIdeal T.V) t) (F : Type) [Field F] [IsAlgClosed F] (f : T.V →+* F), Function.Injective f → ∀ (τ : 𝓞 E →+* F) (N : ℕ), LieMult t.act (spMap f) τ N → letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧ n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  first | exact @GlobalTheory.LieUnif.lieMult_unif | exact GlobalTheory.LieUnif.lieMult_unif | (intros; apply GlobalTheory.LieUnif.lieMult_unif <;> assumption)
