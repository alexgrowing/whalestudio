import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (h : 0 ≤ D.R.m), HEq (S.levRow t 0 h ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram) (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  first | exact @GlobalTheory.FunObj.levRow_zero_eq_lev | exact GlobalTheory.FunObj.levRow_zero_eq_lev | (intros; apply GlobalTheory.FunObj.levRow_zero_eq_lev <;> assumption)
