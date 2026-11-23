import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bigCellExpansion_of_besselFunction_zero : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ), 0 ≤ b → (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) → (∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ := by
  intro P Wp Wq _ _ _ _ _ _ p f b C₃ a₁ hb hm hV
  have hV' : ∀ c : Fin (P.r + 1) → ℂ, p.V f (TBB.bigPt P.r c) = 0 := by
    intro c
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · exact hV c hc.1 hc.2
    · exact Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ hc
  refine ⟨ℤ, inferInstance, fun _ => f, 0, fun _ => 0, fun _ => 0, 0, (P.r + 1) * a₁, 0, rfl, le_rfl,
    fun _ _ => le_rfl, fun _ _ => le_rfl, rfl, rfl, ?_, le_rfl, ?_, fun _ => le_rfl, fun _ => hm⟩
  · intro μ _
    refine ⟨0, ?_, ?_, ?_⟩
    · funext c
      simp [hV' c]
    · simp
    · simp
  · rw [zero_pow (Nat.succ_ne_zero _)]
    exact Real.rpow_nonneg hb _

end GlobalTheory
