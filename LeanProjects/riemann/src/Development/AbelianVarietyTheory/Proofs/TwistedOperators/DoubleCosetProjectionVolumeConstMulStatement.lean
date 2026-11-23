import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetProjection_volume_const_mul : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := by
  first | exact @GlobalTheory.CellLevel.pr_vol | exact GlobalTheory.CellLevel.pr_vol | (intros; apply GlobalTheory.CellLevel.pr_vol <;> assumption)
