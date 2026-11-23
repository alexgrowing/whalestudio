import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def avg {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (h : ℝ → ℝ) (u : ℝ → Mat n → V) : Mat n → V :=
  fun x => ∫ t, (h t : ℂ) • u t x

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

def l1 (f : Mat n → V) : ℝ := ∫ y : G n, ‖f y.val‖ ∂μ

def l2 (f : Mat n → V) : ℝ := Real.sqrt (∫ y : G n, ‖f y.val‖ ^ 2 ∂μ)

def ip [InnerProductSpace ℂ V] (f h : Mat n → V) : ℂ := ∫ y : G n, ⟪f y.val, h y.val⟫_ℂ ∂μ

end Norms

def IsKerC [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (g : ℝ → ℝ) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  ContDiffOn ℝ ∞ k (GLs n) ∧ (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) ∧
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) ∧
    ∀ u, IsWave E u → Cpt (u 0) → ∀ x ∈ GLs n, act μ E k (u 0) x = avg g u x

def FormSymm : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (f h : Mat n → E.V), f ∈ CE E → Cpt f → h ∈ CE E → Cpt h → ip μ (Om f) h = ip μ f (Om h)

def FormBound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ C : ℝ, ∀ f ∈ CE E, Cpt f → (ip μ (Om f) f).re ≤ C * l2 μ f ^ 2

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

def WaveSupp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ R : ℝ,
    (∀ y ∈ GLs n, R < lg y → u 0 y = 0) → ∀ t, ∀ y ∈ GLs n, R + c * (1 + |t|) < lg y → u t y = 0

def WaveLeft : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (a : Mat n), a ∈ GLs n → IsWave E u → IsWave E fun t y => u t (a * y)

def WaveEnergyGrowthBound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ c : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → ∀ t, l2 μ (u t) ≤ Real.exp (c * |t|) * l2 μ (u 0)

def TimeRecip : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (u v : ℝ → Mat n → E.V), IsWave E u → Cpt (u 0) → IsWave E v → Cpt (v 0) → ∀ t, ip μ (u t) (v 0) = ip μ (u 0) (v t)

def OmAvg : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (h : ℝ → ℝ) (T : ℝ), IsWave E u → ContDiff ℝ ∞ h →
    (∀ t, T < |t| → h t = 0) → ∀ x ∈ GLs n, Om (avg h u) x = avg (iteratedDeriv 2 h) u x

def AvgSec : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : KMod n) (u : ℝ → Mat n → E.V) (h : ℝ → ℝ) (T R : ℝ), 0 ≤ T → IsWave E u →
    ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) → (∀ y ∈ GLs n, R < lg y → u 0 y = 0) →
      avg h u ∈ CE E ∧ ∀ y ∈ GLs n, R + c * (1 + T) < lg y → avg h u y = 0

def Recip : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (u v : ℝ → Mat n → E.V) (h : ℝ → ℝ) (T : ℝ), IsWave E u → Cpt (u 0) → IsWave E v → Cpt (v 0) → ContDiff ℝ ∞ h →
      (∀ t, T < |t| → h t = 0) → ip μ (avg h u) (v 0) = ip μ (u 0) (avg h v)

def WaveAverageL2Bounded : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (h : ℝ → ℝ) (T : ℝ), ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) →
      ∃ C : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → l2 μ (avg h u) ≤ C * l2 μ (u 0)

def SobSec : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × Fin n × Fin n)), ∃ (N : ℕ) (C : ℝ), ∀ F ∈ CE E, Cpt F → ∀ x ∈ GLs n,
      ‖Rw w F x‖ ≤ C * ∑ j ∈ range (N + 1), l2 μ (Om^[j] F)

def AverageDerivativeL1Bound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (h : ℝ → ℝ) (T : ℝ) (w : List (Bool × Fin n × Fin n)), ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) →
      ∃ C : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → ∀ x ∈ GLs n, ‖Rw w (avg h u) x‖ ≤ C * l1 μ (u 0)

def ApproxId : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V), (∀ j v, ψ j v ∈ CE E) ∧
      (∃ R, ∀ j v, ∀ y ∈ GLs n, R < lg y → ψ j v y = 0) ∧ (∃ C : ℝ, ∀ j v, l1 μ (ψ j v) ≤ C * ‖v‖) ∧
      (∀ j v, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, ψ j v (k.1 * y) = ψ j (E.ρ k⁻¹ v) y) ∧
      ∀ v, ∀ f ∈ CE E, Cpt f → Tendsto (fun j => ip μ (ψ j v) f) atTop (𝓝 ⟪v, f 1⟫_ℂ)

def LimitStep : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (F : ℕ → Mat n → V) (R : ℝ),
    (∀ j, ContDiffOn ℝ ∞ (F j) (GLs n)) → (∀ j, ∀ y ∈ GLs n, R < lg y → F j y = 0) →
    (∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ j, ∀ x ∈ GLs n, ‖Rw w (F j) x‖ ≤ C) →
    ∃ (l : Filter ℕ) (L : Mat n → V), l.NeBot ∧ l ≤ atTop ∧ ContDiffOn ℝ ∞ L (GLs n) ∧
      (∀ y ∈ GLs n, R < lg y → L y = 0) ∧ TendstoUniformlyOn F L l (GLs n)

def KerBase : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ), IsBump g T → ∃ k, IsKerC μ E g k

def KerExtend : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKerC μ E g k → IsKer μ E [] g k

def KerWord : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E [] g k →
      ∃ k', IsKer μ E w g k'

end GlobalTheory.CompanionTheory.WaveK
