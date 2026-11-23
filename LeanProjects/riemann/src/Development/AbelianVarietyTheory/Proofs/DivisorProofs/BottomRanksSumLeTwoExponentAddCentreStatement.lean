import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksSumLeTwoExponentAddCentre
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre : ∀ (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau), ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤ 2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | exact GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen <;> assumption)
