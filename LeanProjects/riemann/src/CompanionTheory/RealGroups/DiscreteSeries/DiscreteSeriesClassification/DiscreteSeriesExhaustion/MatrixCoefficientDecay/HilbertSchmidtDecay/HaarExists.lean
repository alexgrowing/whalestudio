import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

def HaarExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A → ∃ ν : Measure (PSub ε A), ν.IsHaarMeasure

def KRight : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V),
      (Continuous fun g : S7.UJ ε => famP σ D E hK.gl χ ss i u (S7.toM g)) ∧
      ∃ (T : Finset ((D × List (Fin n)) × (path ⟨D, E, hK.gl⟩ χ ss).V)) (Cf : ℝ),
        ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖famP σ D E hK.gl χ ss i u (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤
          Cf * ∑ p ∈ T, ‖famP σ D E hK.gl χ ss p.1 p.2 (S7.toM g)‖ ^ 2

def Growth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsSqIntOn ε σ →
    ∃ M : ℝ, ∀ (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V), LevelF ε (famP σ D E hK.gl χ ss i u) (-M)

def Pack : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    (∀ (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V), LevelF ε (famP σ D E hK.gl χ ss i u) 0) →
      L2Embedding ε (path ⟨D, E, hK.gl⟩ χ ss)

def LineChain : Prop :=
  ∀ (m : ℕ) (z : Fin m → ℂ) (R R' : ℝ), R ≤ R' → (∀ k, (z k).re ≠ -R) → ∃ C : ℝ, 0 < C ∧
    ∀ F : Fin (m + 1) → ℝ → ℂ, (∀ (k : Fin m) (t : ℝ), 0 ≤ t →
      HasDerivAt (F k.succ) (z k * F k.succ t + F k.castSucc t) t) → (∀ k, Continuous (F k)) →
      (∀ k, ∫⁻ t in Set.Ioi (0 : ℝ), ‖F k t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R' * t)) < ⊤) →
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖F (Fin.last m) t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
        ENNReal.ofReal C * (∑ k, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖F k t‖ₑ ^ 2 +
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖F 0 t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)))

def Assembly : Prop :=
  StepChar → AbsoluteL2Bound → Geo → LineFormula → HaarExists → PolyNilPath → N.RightRule → N.LeftRule → KRight → Growth → Pack → Back

end CompanionTheory.RgExh.Dec.L
