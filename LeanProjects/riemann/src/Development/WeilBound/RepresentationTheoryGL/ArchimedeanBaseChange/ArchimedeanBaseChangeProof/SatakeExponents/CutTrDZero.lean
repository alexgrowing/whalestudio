import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def cutTrD (D : Dom E a b) (τ : ℝ) (φ : H E a b → ℂ) : ℂ :=
  ∫ x, chiT τ x.1 * chiT τ x.2 * kerTw2 φ x x ∂D.ν

def trM {ι : Type} [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) : H E a b → ℂ :=
  fun y => ∑ i, ∑ j, Φ i j y * M j i

def SBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ),
  IsTestM Φ₁ → IsTestM Φ₂ → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → ∃ (C : ℝ) (N : ℕ), ∀ (τ : ℝ)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)), 0 ≤ τ → IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → ‖cutTrD D τ (trM Φ M)‖ ≤ C * (1 + τ) ^ N * ‖U‖

def Bridge : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
  (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (F₁ : Set (GA E a))
  (F₂ : Set (GA E b)), IsFundamentalDomain (ratGL E a).range F₁ μ₁ → IsFundamentalDomain (ratGL E b).range F₂ μ₂ →
  ∃ D : Dom E a b, D.F = F₁ ×ˢ F₂ ∧ ∀ τ φ, cutTrD D τ φ = cutTr2 μ₁ μ₂ F₁ F₂ τ φ

def OpEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι],
  (∀ Φ : Matrix ι ι (H E a b → ℂ), IsTestM Φ → ∃! T, IsROp D Φ T) ∧
  ∀ (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) T₁ T₂, IsTestM Φ₁ → IsTestM Φ₂ → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
    IsTestM (mulM D.μ Φ₁ Φ₂) ∧ IsROp D (mulM D.μ Φ₁ Φ₂) (T₁ * T₂) ∧
      IsROp D (adjM Φ₁) (ContinuousLinearMap.adjoint T₁)

def Growth : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (a b : ℕ)
  [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
  (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure],
  ∃ D : Dom E a b, ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (r₀ r₁ : ℝ), IsTestM Φ₁ → IsTestM Φ₂ →
    IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ)
      (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
      IsTest2 (trM Φ M) (r₀ + k * r₁) → ‖ellSum2 μ₁ μ₂ (trM Φ M)‖ ≤ C * (1 + k) ^ N * ‖U‖

end PositivityTheory.Rg.BcB.F

end
