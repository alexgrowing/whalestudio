import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_weylElement_generate_unitary : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  first | exact @GlobalTheory.KSp.sieg_weyl_generate | exact GlobalTheory.KSp.sieg_weyl_generate | (intros; apply GlobalTheory.KSp.sieg_weyl_generate <;> assumption)
