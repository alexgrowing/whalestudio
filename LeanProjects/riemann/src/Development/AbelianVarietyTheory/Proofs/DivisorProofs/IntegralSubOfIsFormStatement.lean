import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_sub_of_isForm' : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β →
    A.integral (α - β) = A.integral α - A.integral β := by
  first | exact @GlobalTheory.CxForm.HolAtlas.integral_sub_of_isForm | exact GlobalTheory.CxForm.HolAtlas.integral_sub_of_isForm | (intros; apply GlobalTheory.CxForm.HolAtlas.integral_sub_of_isForm <;> assumption)
