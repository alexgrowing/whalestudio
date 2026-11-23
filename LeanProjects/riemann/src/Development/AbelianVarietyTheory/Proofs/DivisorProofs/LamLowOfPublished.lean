import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookLogSumSubSizeTermLeLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamilyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.BigTop

theorem lamLow_of_classicalTheorems : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → GlobalTheory.BigTop.LamLow := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (Formalism.MainNotions.DIV.closed_Csz_ge FamHyp 8).imp ?_
  intro eps Fm CH _ h8
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.thetaLift_weightSizes_eventually_along_family eps Fm
  refine ⟨x0, fun x hx hle i p hp C => ?_⟩
  have hS : ∀ j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := hx0 x hx hle i
  refine GlobalTheory.T.finiteness_inputs_real_data_three h1 h2 h3 h4 h5 h6 h7 (T := p.T) (R := p.R) (F := p.F) p.κ p.v₀ p.O 1 (Fm.L x i).sc.b C CH
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
