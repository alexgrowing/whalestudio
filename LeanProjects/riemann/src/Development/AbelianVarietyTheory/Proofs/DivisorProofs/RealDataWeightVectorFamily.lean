import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.Divisors.Params
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesUnitEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestPositiveLevelsKappaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialLFunctionFromPrintResultsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingMethodConsequenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentityStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Stage4

theorem stage4 : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  intro P hRSW hHL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hT hG hM hRow hLv hPos
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod P.q9
  obtain ⟨hOk, hGU, hGE, hBlk, hA, _hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  obtain ⟨hLT, hLTB, _hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  obtain ⟨hLevW, hPartsW, hHecke, hSep, _hTr⟩ := GlobalTheory.T.lift_test_positive_levels_kappa P R F hT hM hG.unif hLT hLv hPos
  have hOnto := GlobalTheory.T.partial_L_function_of_hypotheses P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hRSW hHL (s := 1) R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hOk.2 hGE hG.unif
  obtain ⟨fw, hBar⟩ := hG.fw
  have hGal : (R.toCx3 F).GalD F.cr false :=
    GlobalTheory.T.doubling_method_consequence hE P.q1 P.q2 P.q13 P.q11 P.q9 P.q14 P.q10 P.q7 P.q4 T R F κ v₀ O 1 hT.ok hSep hT.char hT.ex hT.params
      hT.phs hT.std fw hBar hG.ioExt hG.pins (fun i => (hG.oneMap i).1) hG.phase hOk.1 hOk.2 hHecke hGU hGE hBlk hRow hLT hLTB
      hOnto hPos.1 hPos.2 hG.unif hLevW hA hPartsW
  exact ⟨hGal, GlobalTheory.T.liftScalar_pos_allPlaces_of_conjugateIdentity R F hT.ok hT.char hT.ex hPos hGal hG.unif hLTB hGE⟩

end GlobalTheory.Stage4
