import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubini
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  first | exact @GlobalTheory.CellMass.cell_fubini | exact GlobalTheory.CellMass.cell_fubini | (intros; apply GlobalTheory.CellMass.cell_fubini <;> assumption)
