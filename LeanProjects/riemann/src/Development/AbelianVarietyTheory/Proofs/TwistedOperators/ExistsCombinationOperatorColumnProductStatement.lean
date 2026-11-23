import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combinationOperator_columnProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  first | exact @GlobalTheory.LocAsm.exists_comb_op | exact GlobalTheory.LocAsm.exists_comb_op | (intros; apply GlobalTheory.LocAsm.exists_comb_op <;> assumption)
