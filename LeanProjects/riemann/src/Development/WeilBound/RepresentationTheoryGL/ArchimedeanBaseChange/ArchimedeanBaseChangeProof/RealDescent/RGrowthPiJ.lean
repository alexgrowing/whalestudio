import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

def GrowthPiJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (n : ℕ), 1 ≤ n →
  ∀ [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] [MeasurableSpace (GA E 0)] [BorelSpace (GA E 0)]
  (μ₁ : Measure (GA E n)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E 0)) [μ₂.IsHaarMeasure],
  ∃ D : Dom E n 0, (∀ F : H E n 0 → ℂ, Continuous F → HasCompactSupport F → ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂μ₂ ∂μ₁) ∧
    ∀ π : CuspSub E n, ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (r₀ r₁ ε : ℝ), IsTestM Φ₁ → IsTestM Φ₂ →
    (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ)
      (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
      (∀ f ∈ piSp D π ι, U f ∈ piSp D π ι) → (∀ f ∈ (piSp D π ι)ᗮ, U f ∈ (piSp D π ι)ᗮ) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → IsTwTr D.μ π (trM Φ M) t →
      ‖ellSum2 μ₁ μ₂ (trM Φ M) - t / 2‖ ≤ C * (1 + k) ^ N * ‖U ∘L (piSp D π ι)ᗮ.subtypeL‖ + C * ‖U‖ * ε ^ k

def RGrowthPiJ : Prop := D4.EllFormula2J → PositivityTheory.Rg.BcB.E1.SFun → PiVecEx → PiInv → GrowthPiJ

end PositivityTheory.Rg.BcB.Desc

end
