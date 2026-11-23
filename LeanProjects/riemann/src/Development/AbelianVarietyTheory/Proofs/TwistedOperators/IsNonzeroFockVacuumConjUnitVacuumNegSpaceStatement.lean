import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f → GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  first | exact @GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | exact GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | (intros; apply GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg <;> assumption)
