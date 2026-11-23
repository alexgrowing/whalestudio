import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharIntertwiningUnif
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_char_intertwining_unif : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (ν β : kˣ →* ℂˣ), IsSmoothChar ν → IsUnitaryChar ν → IsSmoothChar β → IsUnitaryChar β →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (R : GL (Fin (a + a')) k → W → W)
      (L : (Matrix (Fin a) (Fin (a + a')) k → ℂ) →ₗ[ℂ] W),
      (∀ (g : GL (Fin a) k), ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k), L (GlobalTheory.SplitFlip.omA ν β g 1 Ψ) = L Ψ) →
      (∀ (h : GL (Fin (a + a')) k), ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k),
        L (GlobalTheory.SplitFlip.omA ν β 1 h Ψ) = R h (L Ψ)) →
      ∃ T : IndSp (e2 a a') (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * β) β)) →ₗ[ℂ] W,
        (∀ h y, T (detInd a a' (ν * β) β h y) = R h (T y)) ∧
        ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k), ∃ y, L Ψ = T y := by
  first | exact @GlobalTheory.DetIndScal.factor_through_detInd | exact GlobalTheory.DetIndScal.factor_through_detInd | (intros; apply GlobalTheory.DetIndScal.factor_through_detInd <;> assumption)
