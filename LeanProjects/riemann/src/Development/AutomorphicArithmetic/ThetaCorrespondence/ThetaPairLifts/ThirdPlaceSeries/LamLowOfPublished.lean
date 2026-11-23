import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealDataThree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.BigTop
theorem lamLow_of_hypotheses_alt_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (Formalism.MainNotions.DIV.closed_Csz_ge FamHyp 8).imp ?_
  intro eps Fm CH _ h8
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.thetaLift_weightSizes_eventually_along_family eps Fm
  refine ⟨x0, fun x hx hle i p hp C => ?_⟩
  have hS : ∀ j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := hx0 x hx hle i
  refine _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt h1 h2 h3 h4 h5 h6 h7 (T := p.T) (R := p.R) (F := p.F) p.κ p.v₀ p.O 1 (Fm.L x i).sc.b C CH
    hp.ok hp.sep p.charW hp.exAt hp.prim p.phsOne p.stdChar p.fw p.bar hp.ioExt p.pins (fun j => (hp.oneMap j).1) p.phase hS
    ?_ ?_ ⟨_, ⟨Fm.params x hx i⟩⟩ p.stdV
  · intro j
    have := GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound (Fm.D x i) (Fm.L x i) p.Del p.h0 Fm.Csz j h8 (hS j)
    exact this
  · intro j
    show _ - C * 0 ≤ _
    rw [mul_zero, sub_zero]
    exact le_rfl
end GlobalTheory.BigTop
end
end
