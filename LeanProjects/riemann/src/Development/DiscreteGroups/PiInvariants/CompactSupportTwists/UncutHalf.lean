import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def lInt0 {ι : Type} [Fintype ι] (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x : H E a b) : ℂ :=
  ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))

def IsPiPart {n : ℕ} {ι : Type} [Fintype ι] (D : Dom E n 0) (π : CuspSub E n)
    (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) : Prop :=
  (∀ f ∈ piSp D π ι, Uπ f = U f) ∧ ∀ f ∈ (piSp D π ι)ᗮ, Uπ f = 0

def KerSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (π : CuspSub E n)
  (ι : Type) [Fintype ι] (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D) (τ C : ℝ) (N : ℕ),
  (∀ V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, Integrable (lInt D k₁ k₂ τ V) D.ν ∧
    ‖∫ x, lInt D k₁ k₂ τ V x ∂D.ν‖ ≤ C * (1 + τ) ^ N * ‖V‖) →
  ∀ U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, (∀ f ∈ piSp D π ι, U f ∈ piSp D π ι) →
    (∀ f ∈ (piSp D π ι)ᗮ, U f ∈ (piSp D π ι)ᗮ) →
    ∃ Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D, IsPiPart D π U Uπ ∧ ‖Uπ‖ ≤ ‖U‖ ∧
      ‖∫ x, lInt D k₁ k₂ τ U x ∂D.ν - ∫ x, lInt D k₁ k₂ τ Uπ x ∂D.ν‖ ≤
        C * (1 + τ) ^ N * ‖U ∘L (piSp D π ι)ᗮ.subtypeL‖

def UncutHalf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ →
  ∀ (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → IsTwTr D.μ π (trM Φ M) t →
    Integrable (lInt0 D k₁ k₂ Uπ) D.ν ∧ ∫ x, lInt0 D k₁ k₂ Uπ x ∂D.ν = t / 2

def DomOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] [MeasurableSpace (GA E 0)] [BorelSpace (GA E 0)]
  (μ₁ : Measure (GA E n)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E 0)) [μ₂.IsHaarMeasure], ∃ (F₁ : Set (GA E n))
  (F₂ : Set (GA E 0)) (D : Dom E n 0), IsFundamentalDomain (ratGL E n).range F₁ μ₁ ∧
    IsFundamentalDomain (ratGL E 0).range F₂ μ₂ ∧ (∀ τ φ, cutTrD D τ φ = PositivityTheory.Rg.BcB.cutTr2 μ₁ μ₂ F₁ F₂ τ φ) ∧
    ∀ F : H E n 0 → ℂ, Continuous F → HasCompactSupport F → ∫ x, F x ∂D.μ = ∫ x₁, ∫ x₂, F (x₁, x₂) ∂μ₂ ∂μ₁

end DiscreteGroups.T1.G

end
