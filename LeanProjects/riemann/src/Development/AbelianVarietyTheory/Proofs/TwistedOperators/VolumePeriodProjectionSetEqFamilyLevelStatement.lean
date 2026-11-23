import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumePeriodProjectionSetEqFamilyLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_periodProjectionSet_eq_familyLevel : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ (hj : j < D.R.m) (ν : Measure (GfC (ch.G.V (.top j)))),
    ν.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      ν.real (prSet ch.G j ⟨b j, hb⟩) = c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.S.toGridChoice.levTop t Φ β j hj} := by
  first | exact @GlobalTheory.PrLevel.vol_prSet | exact GlobalTheory.PrLevel.vol_prSet | (intros; apply GlobalTheory.PrLevel.vol_prSet <;> assumption)
