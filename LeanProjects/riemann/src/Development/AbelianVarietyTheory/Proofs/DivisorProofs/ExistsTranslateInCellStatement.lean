import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCell
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_inCell' : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))), ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  first | exact @GlobalTheory.KSp.exists_translate_inCell | exact GlobalTheory.KSp.exists_translate_inCell | (intros; apply GlobalTheory.KSp.exists_translate_inCell <;> assumption)
