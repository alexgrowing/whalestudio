import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinitePartDenominatorLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePart_denominator_le_height_pow : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * height V g ^ A ∧ ∀ i j, (d : Lev.EAf D) * (Lev.finE V g).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PointDenom.exists_denom_le_height_pow | exact GlobalTheory.PointDenom.exists_denom_le_height_pow | (intros; apply GlobalTheory.PointDenom.exists_denom_le_height_pow <;> assumption)
