import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetFieldIsoTransport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_field_iso_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (e : k ≃+* k'),
    Continuous e → Continuous e.symm → ∀ (a a' l n : ℕ) (h : l + n ≤ a + a') (α₀ β₀ : kˣ →* ℂˣ) (α β : k'ˣ →* ℂˣ),
    (∀ y, α₀ y = α (Units.map e.toRingHom.toMonoidHom y)) → (∀ y, β₀ y = β (Units.map e.toRingHom.toMonoidHom y)) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (Q : Representation ℂ (GL (Fin n) k) W),
      IsSubquotient Q ((jacU (tripPlace h) (detInd a a' α₀ β₀)).comp (midHom k l n (a + a'))) →
      IsSubquotient (Q.comp (GlobalTheory.LFun.SplitTie.glEquiv n e).symm.toMonoidHom)
        ((jacU (tripPlace h) (detInd a a' α β)).comp (midHom k' l n (a + a'))) := by
  first | exact @GlobalTheory.MidJacTransport.isSubquotient_midJacU_transport | exact GlobalTheory.MidJacTransport.isSubquotient_midJacU_transport | (intros; apply GlobalTheory.MidJacTransport.isSubquotient_midJacU_transport <;> assumption)
