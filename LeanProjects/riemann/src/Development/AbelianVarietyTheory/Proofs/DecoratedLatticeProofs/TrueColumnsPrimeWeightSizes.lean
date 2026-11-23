import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnWeightSpreadLeTwoMulScaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WtsOkAndSizes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLeLOfLeCond
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem GlobalTheory.CoreHt.sizes_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  intro B X I h l Z L CY hR hX' hx hT
  have hW := (GlobalTheory.Mem.wts_ok_and_sizes B X).2
  have hF := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  obtain ⟨P⟩ := hR.1
  have hfN := GlobalTheory.ColumnNormCompare.SizeRows.f_mul_N_le_b P hR.2.2.2.1.1
  have hb1 := GlobalTheory.ColumnNormCompare.SizeRows.one_le_b L.sc
  refine ⟨hW.g_big, fun u => hT u, ?_, GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale I h l Z L CY hR hX' hx⟩
  have hab : 2 * L.sc.b ≤ L.sc.a := by
    show 2 * L.sc.b ≤ L.sc.x * L.sc.b
    nlinarith
  have hfN' : ((B.fields.f : ℝ)) * (B.R.N B.R.m : ℝ) ≤ L.sc.b := by
    rw [hF]; exact hfN
  push_cast
  linarith
