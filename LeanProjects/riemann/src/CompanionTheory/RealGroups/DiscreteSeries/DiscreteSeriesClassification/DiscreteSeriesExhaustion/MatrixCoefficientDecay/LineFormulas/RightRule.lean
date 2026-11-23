import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec.N

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

def OdeA : Prop :=
  ∀ (z : ℂ) (s : ℝ), z.re < s → ∀ f g : ℝ → ℂ, (∀ t, 0 ≤ t → HasDerivAt f (z * f t + g t) t) → Continuous g →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖g t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤ →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤

def OdeB : Prop :=
  ∀ (z : ℂ) (s s' : ℝ), s < z.re → s' ≤ z.re → ∀ f g : ℝ → ℂ, (∀ t, 0 ≤ t → HasDerivAt f (z * f t + g t) t) →
    Continuous g →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖g t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤ →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s' * t))) < ⊤ →
    (∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))) < ⊤

def RightRule : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε X →
      ∀ g, Formalism.REAL.inUJ ε g →
        HasDerivAt (fun t : ℝ => (famP σ D E hK.gl χ ss i u) (g * NormedSpace.exp ((t : ℂ) • X)))
          ((famP σ D E hK.gl χ ss i (∑ a, ∑ b, X a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b u)) g) 0

def LeftRule : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ i : D × List (Fin n), ∃ l : Fin n → Fin n → (D × List (Fin n)) →₀ ℂ,
      ∀ (a b : Fin n) (u : (path ⟨D, E, hK.gl⟩ χ ss).V) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
        (famP σ D E hK.gl χ ss i ((path ⟨D, E, hK.gl⟩ χ ss).E a b u)) g =
          ∑ c, ∑ d, (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c d *
            (l c d).sum fun i' r => r * (famP σ D E hK.gl χ ss i' u) g

end CompanionTheory.RgExh.Dec.N
