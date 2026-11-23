import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetInducedTwist
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_det_induced_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' l n : ℕ)
    (h : l + n ≤ a + a') (x : ℝ), ∃ z : ℝ, ∀ (α β : kˣ →* ℂˣ)
    (W : Type) [AddCommGroup W] [Module ℂ W] (Q : Representation ℂ (GL (Fin n) k) W),
      IsSubquotient Q ((jacU (tripPlace h) (detInd a a' α β)).comp (midHom k l n (a + a'))) →
      IsSubquotient (twist Q (detChar (Fin n) (absPow k (x : ℂ))))
        (midJac l n (a + a') h (detInd a a' (α * absPow k (z : ℂ)) (β * absPow k (z : ℂ)))) := by
  first | exact @GlobalTheory.MidJacTwist.isSubquotient_midJac_twist | exact GlobalTheory.MidJacTwist.isSubquotient_midJac_twist | (intros; apply GlobalTheory.MidJacTwist.isSubquotient_midJac_twist <;> assumption)
