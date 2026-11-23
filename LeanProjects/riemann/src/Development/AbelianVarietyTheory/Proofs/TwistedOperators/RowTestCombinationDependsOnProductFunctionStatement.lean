import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_combination_depends_on_product_function : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 := by
  first | exact @GlobalTheory.CombDet.comb_det | exact GlobalTheory.CombDet.comb_det | (intros; apply GlobalTheory.CombDet.comb_det <;> assumption)
