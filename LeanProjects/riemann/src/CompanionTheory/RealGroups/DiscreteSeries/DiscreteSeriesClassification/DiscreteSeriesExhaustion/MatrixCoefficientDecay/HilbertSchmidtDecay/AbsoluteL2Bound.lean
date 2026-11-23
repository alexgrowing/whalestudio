import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.HaarPolar

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def aT (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((t : ℂ) • A)

def LevelF (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : ℝ) : Prop :=
  ∫⁻ g : S7.UJ ε, ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) ∂(Measure.haar) < ⊤

def Chain (ε : Fin n → Bool) (S : Set (Matrix (Fin n) (Fin n) ℂ → ℂ)) (A : Matrix (Fin n) (Fin n) ℂ) (Z : Finset ℂ)
    (f f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (z : Fin m → ℂ) (F : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ k, z k ∈ Z) ∧ (∀ k, F k ∈ S) ∧ F (Fin.last m) = f ∧ F 0 = f₀ ∧
    ∀ (k : Fin m) (g : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), ReciprocityTheory.ChartRestriction.DS.inUJ ε g →
      HasDerivAt (fun s : ℝ => F k.succ (g * aT A s)) (z k * F k.succ (g * aT A t) + F k.castSucc (g * aT A t)) t

def AbsoluteL2Bound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (m : ℕ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (ν : ∀ j, Measure (PSub ε (A j))) (τ : Fin m → S7.UJ ε → ℝ)
    (r : Fin m → ℝ) (Z : Fin m → Finset ℂ) (M c₁ R₀ C : ℝ),
    0 < c₁ →

    (∀ j, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable (fun g : S7.UJ ε => F (S7.toM g)) → (∀ (g : S7.UJ ε) (k : S7.KG ε), F (S7.toM g * S7.toMK k) = F (S7.toM g)) →
      ∫⁻ g : S7.UJ ε, F (S7.toM g) ∂Measure.haar = κ * ∫⁻ x in {x : PSub ε (A j) | τ j x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j)) →

    (∀ j, Continuous (τ j)) →
    (∀ j (x y : PSub ε (A j)) (k : S7.KG ε), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * S7.toMK k → τ j y = τ j x) →

    (∀ j (x : PSub ε (A j)) (t : ℝ), ∃ y : PSub ε (A j), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t ∧
      τ j y = τ j x + t) →

    (∃ U : Fin m → Set (S7.UJ ε), (∀ j, MeasurableSet (U j)) ∧ (∀ j g (k : S7.KG ε), g ∈ U j → g * (k : S7.UJ ε) ∈ U j) ∧
      (∀ g : S7.UJ ε, R₀ < Formalism.REAL.hs (S7.toM g) → ∃ j, g ∈ U j) ∧
      ∀ j (x : PSub ε (A j)), (x : S7.UJ ε) ∈ U j → c₁ * Real.log (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ≤ τ j x) →

    (∀ j (x : PSub ε (A j)) (t : ℝ), 0 ≤ τ j x → 0 ≤ t →
      C⁻¹ * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ≤ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ∧
        Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ≤ C * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) →

    (∀ f ∈ S, Continuous fun g : S7.UJ ε => f (S7.toM g)) →
    (∀ f ∈ S, ∃ (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ), (∀ h ∈ T, h ∈ S) ∧
      ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖f (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2) →

    (∀ f ∈ S, ∀ j, ∃ (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)), Chain ε S (A j) (Z j) f f₀ ∧ (∀ h ∈ T, h ∈ S) ∧
      ∀ x : PSub ε (A j), 0 ≤ τ j x →
        ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖) →

    (∀ f ∈ S, ∀ j, ∀ᵐ (x : PSub ε (A j)) ∂(ν j), (∫⁻ t in Set.Ioi (0 : ℝ),
      ‖f (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + 1) * t))) < ⊤) →

    (∀ f ∈ S, LevelF ε f (-M)) →
      ∀ f ∈ S, LevelF ε f 0

def OdeStep : Prop :=
  ∀ (z : ℂ) (R : ℝ), z.re ≠ -R → ∃ C : ℝ, 0 < C ∧ ∀ (u g : ℝ → ℂ) (R' : ℝ),
    (∀ t, HasDerivAt u (z * u t + g t) t) → Continuous g → (-R < z.re → R ≤ R' ∧
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R' * t)) < ⊤) →
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖u t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)) ≤
        ENNReal.ofReal C * (∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 +
          ∫⁻ t in Set.Ioi (0 : ℝ), ‖g t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * R * t)))

def LineFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (ν : Measure (PSub ε A)) (τ : S7.UJ ε → ℝ),
    IsGrad ε A → ν.IsHaarMeasure → Continuous τ →
    (∀ (x : PSub ε A) (t : ℝ) (y : PSub ε A), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT A t → τ y = τ x + t) →
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable (fun g : S7.UJ ε => F (S7.toM g)) →
      (∀ (g : S7.UJ ε) (k : S7.KG ε), F (S7.toM g * S7.toMK k) = F (S7.toM g)) →
      ∫⁻ g : S7.UJ ε, F (S7.toM g) ∂Measure.haar = κ * ∫⁻ x in {x : PSub ε A | τ x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT A t) * ENNReal.ofReal (Real.exp (2 * rhoA A * t))) ∂ν

def nilpC (A : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Y | ∃ Y₁ Y₂ : Matrix (Fin n) (Fin n) ℂ, Y = Y₁ + Y₂ ∧ A * Y₁ - Y₁ * A = -Y₁ ∧ A * Y₂ - Y₂ * A = -((2 : ℂ) • Y₂)}

def Geo : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (τ : Fin m → S7.UJ ε → ℝ) (c₁ R₀ C : ℝ),
    0 < c₁ ∧ (∀ j, IsGrad ε (A j)) ∧ (∀ j, Continuous (τ j)) ∧
    (∀ j (x y : PSub ε (A j)) (k : S7.KG ε), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * S7.toMK k → τ j y = τ j x) ∧
    (∀ j (x : PSub ε (A j)) (t : ℝ), ∃ y : PSub ε (A j), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t) ∧
    (∀ j (x : PSub ε (A j)) (t : ℝ) (y : PSub ε (A j)), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t →
      τ j y = τ j x + t) ∧
    (∃ U : Fin m → Set (S7.UJ ε), (∀ j, MeasurableSet (U j)) ∧ (∀ j g (k : S7.KG ε), g ∈ U j → g * (k : S7.UJ ε) ∈ U j) ∧
      (∀ g : S7.UJ ε, R₀ < Formalism.REAL.hs (S7.toM g) → ∃ j, g ∈ U j) ∧
      ∀ j (x : PSub ε (A j)), (x : S7.UJ ε) ∈ U j → c₁ * Real.log (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ≤ τ j x) ∧
    (∀ j (x : PSub ε (A j)) (t : ℝ), 0 ≤ τ j x → 0 ≤ t →
      C⁻¹ * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ≤ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ∧
        Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ≤ C * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ∧
    (∀ j (x : PSub ε (A j)) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilpC (A j) → 0 ≤ τ j x →
      Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Y * (S7.toM (x : S7.UJ ε))⁻¹) ≤ C * Real.exp (-2 * τ j x) * Formalism.REAL.hs Y)

def actM (X : GMod n) (Y : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ X.V := ∑ a, ∑ b, Y a b • X.E a b

def PolyNilPath : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (χ : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ), HasChar X χ → IsGrad ε A →
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ u : X.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → X.V),
      (∀ k, Y k ∈ nilpC A) ∧ Polynomial.aeval (actM X A) p u = ∑ k, actM X (Y k) (v k)

end CompanionTheory.RgExh.Dec.L
