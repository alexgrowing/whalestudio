import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_range_norm_of_not_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ), x ∉ (Units.map (Algebra.norm F : E →* F)).range → y ∉ (Units.map (Algebra.norm F : E →* F)).range → x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  first | exact @GlobalTheory.KSp.NormIndex.mul_mem_range_norm | exact GlobalTheory.KSp.NormIndex.mul_mem_range_norm | (intros; apply GlobalTheory.KSp.NormIndex.mul_mem_range_norm <;> assumption)
