import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec.N.S

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool}

def W (A : Matrix (Fin n) (Fin n) ℂ) : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, Vm A]

def rk (A : Matrix (Fin n) (Fin n) ℂ) : ℕ := Module.finrank ℂ (Vm A)

def modA (A : Matrix (Fin n) (Fin n) ℂ) (m : Formalism.REAL.UJ ε) : ℝ≥0∞ :=
  ENNReal.ofReal (GlobalTheory.Count.layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id)

def FlagFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    1 ≤ rk A ∧ IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) ∧ rhoA A = (rk A : ℝ) * ((n : ℝ) - rk A)

def PSubEq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A → ∀ g : Formalism.REAL.UJ ε,
    g ∈ PSub ε A ↔ ∃ u ∈ flagN ε (W A), ∃ m ∈ flagM ε (W A), g = u * m

def LineFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∃ (a : ℝ → Formalism.REAL.UJ ε) (τ : Formalism.REAL.UJ ε → ℝ), Continuous a ∧ Measurable τ ∧
      (∀ t, uMat (a t) = NormedSpace.exp ((t : ℂ) • A)) ∧ (∀ s t, a (s + t) = a s * a t) ∧
      (∀ t, a t ∈ flagM ε (W A)) ∧ (∀ t, ∀ m ∈ flagM ε (W A), m * a t = a t * m) ∧
      (∀ m ∈ flagM ε (W A), ∀ t, modA A (m * a t) = modA A m * ENNReal.ofReal (Real.exp (2 * rhoA A * t))) ∧
      (∀ u ∈ flagN ε (W A), ∀ m ∈ flagM ε (W A), ∀ t, τ (u * m * a t) = τ m + t)

def Slab : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μN μM : Measure G) [SFinite μN] [SFinite μM]
    (S : Set G) (a : ℝ → G) (δ : G → ℝ≥0∞) (τ : G → ℝ) (c : ℝ), MeasurableSet S → μM Sᶜ = 0 → Measurable a →
    Measurable δ → Measurable τ → (∀ s t, a (s + t) = a s * a t) → (∀ m ∈ S, ∀ t, m * a t ∈ S) →
    (∀ t, μM.map (· * a t) = μM) → (∀ m ∈ S, ∀ t, δ (m * a t) = δ m * ENNReal.ofReal (Real.exp (2 * c * t))) →
    (∀ m ∈ S, ∀ t, τ (m * a t) = τ m + t) → (∀ m ∈ S, δ m ≠ 0) →
    ∀ F : G → ℝ≥0∞, Measurable F → (∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN) < ⊤ →
      ∀ᵐ p ∂(μN.prod μM), (∫⁻ t in Set.Ioi (0 : ℝ), F (p.1 * p.2 * a t) * ENNReal.ofReal (Real.exp (2 * c * t))) < ⊤

def Fub : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∃ (μN μM : Measure (Formalism.REAL.UJ ε)), SFinite μN ∧ SFinite μM ∧ μM (flagM ε (W A))ᶜ = 0 ∧
      (∀ a : Formalism.REAL.UJ ε, a ∈ flagM ε (W A) → (∀ m ∈ flagM ε (W A), m * a = a * m) → μM.map (· * a) = μM) ∧
      (∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
        (∀ g, ∀ k ∈ Formalism.REAL.KG ε, F (g * k) = F g) →
        ∫⁻ g, F g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN) ∧
      ∀ μ, IsParHaar ε A μ → ∀ E : Set (Formalism.REAL.UJ ε), MeasurableSet E →
        (μN.prod μM) {p | p.1 * p.2 ∈ E} = 0 → μ E = 0

def KMaj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    CompanionTheory.D.LK.IsKMod ε σ D E → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsSqIntOn ε σ → ∀ (u : D) (ξ : H),
      ∃ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F ∧ (∀ g, ∀ k ∈ Formalism.REAL.KG ε, F (g * k) = F g) ∧
        (∫⁻ g, F g ∂(Formalism.REAL.muG ε)) < ⊤ ∧ ∀ g : Formalism.REAL.UJ ε, ‖⟪ξ, σ (uMat g) u⟫_ℂ‖ₑ ^ 2 ≤ F g

def StartOf : Prop := FlagFacts → PSubEq → LineFacts → Slab → Fub → KMaj → Start

end CompanionTheory.RgExh.Dec.N.S
