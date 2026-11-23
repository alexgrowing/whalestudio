import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Base

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def adjK (E : KMod n) (A : E.V →L[ℂ] E.V) : E.V →L[ℂ] E.V :=
  haveI := FiniteDimensional.complete ℂ E.V
  ContinuousLinearMap.adjoint A

def IsApprox [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V)) : Prop :=
  (∀ j v, ψ j v ∈ CE E) ∧
    (∃ R, ∀ j v, ∀ y ∈ GLs n, R < lg y → ψ j v y = 0) ∧ (∃ C : ℝ, ∀ j v, l1 μ (ψ j v) ≤ C * ‖v‖) ∧
    (∀ j v, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, ψ j v (k.1 * y) = ψ j (E.ρ k⁻¹ v) y) ∧
    ∀ v, ∀ f ∈ CE E, Cpt f → Tendsto (fun j => ip μ (ψ j v) f) atTop (𝓝 ⟪v, f 1⟫_ℂ)

def IsFam (E : KMod n) (g : ℝ → ℝ) (ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V)) (Θ : ℕ → Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  (∀ j, ContDiffOn ℝ ∞ (Θ j) (GLs n)) ∧ (∃ R, ∀ j, ∀ y ∈ GLs n, R < lg y → Θ j y = 0) ∧
    (∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ j, ∀ x ∈ GLs n, ‖Rw w (Θ j) x‖ ≤ C) ∧
    ∀ j v, ∃ W, IsWave E W ∧ (∀ y ∈ GLs n, W 0 y = ψ j v y) ∧ ∀ y ∈ GLs n, Θ j y v = avg g W y

def WaveLin : Prop :=
  ∀ (n : ℕ) (E : KMod n) (ι : Type) [Fintype ι] (c : ι → ℂ) (U : ι → ℝ → Mat n → E.V), (∀ i, IsWave E (U i)) →
    IsWave E fun t y => ∑ i, c i • U i t y

def AvgLin : Prop :=
  ∀ (n : ℕ) (E : KMod n) (ι : Type) [Fintype ι] (c : ι → ℂ) (U : ι → ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ),
    IsBump g T → (∀ i, IsWave E (U i)) → ∀ x ∈ GLs n,
      avg g (fun t y => ∑ i, c i • U i t y) x = ∑ i, c i • avg g (U i) x

def RwLin : Prop :=
  ∀ (n : ℕ) (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ι : Type) [Fintype ι] (L : ι → V →L[ℝ] W) (f : ι → Mat n → V), (∀ i, ContDiffOn ℝ ∞ (f i) (GLs n)) →
    ∀ (w : List (Bool × Fin n × Fin n)), ∀ x ∈ GLs n, Rw w (fun y => ∑ i, L i (f i y)) x = ∑ i, L i (Rw w (f i) x)

def FamStep : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ) (ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V)), IsBump g T → IsApprox μ E ψ → ∃ Θ, IsFam E g ψ Θ

def EquivStep : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ) (ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V)) (Θ : ℕ → Mat n → (E.V →L[ℂ] E.V)),
    IsBump g T → IsApprox μ E ψ → IsFam E g ψ Θ → ∀ j v (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ y ∈ GLs n,
      Θ j (y * k.1) v = E.ρ k⁻¹ (Θ j y v) ∧ Θ j (k.1 * y) v = Θ j y (E.ρ k⁻¹ v)

def LimitAdj : Prop :=
  ∀ (n : ℕ) (E : KMod n) (Θ : ℕ → Mat n → (E.V →L[ℂ] E.V)) (L : Mat n → (E.V →L[ℂ] E.V)) (l : Filter ℕ), l.NeBot →
    (∀ j v (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ y ∈ GLs n,
      Θ j (y * k.1) v = E.ρ k⁻¹ (Θ j y v) ∧ Θ j (k.1 * y) v = Θ j y (E.ρ k⁻¹ v)) →
    ContDiffOn ℝ ∞ L (GLs n) → TendstoUniformlyOn Θ L l (GLs n) →
    ContDiffOn ℝ ∞ (fun y => adjK E (L y)) (GLs n) ∧
      ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
        adjK E (L (k₁.1 * y * k₂.1)) = E.ρ k₁ * adjK E (L y) * E.ρ k₂

def PairLim : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (f : Mat n → E.V) (Θ : ℕ → Mat n → (E.V →L[ℂ] E.V)) (L : Mat n → (E.V →L[ℂ] E.V)) (l : Filter ℕ) (v : E.V),
    ContinuousOn f (GLs n) → Cpt f → (∀ j, ContinuousOn (Θ j) (GLs n)) → ContinuousOn L (GLs n) →
    TendstoUniformlyOn Θ L l (GLs n) → Tendsto (fun j => ip μ f fun y => Θ j y v) l (𝓝 (ip μ f fun y => L y v))

def PairAct : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (f : Mat n → E.V) (L : Mat n → (E.V →L[ℂ] E.V)) (v : E.V), ContinuousOn f (GLs n) → Cpt f → ContinuousOn L (GLs n) →
    ⟪act μ E (fun y => adjK E (L y)) f 1, v⟫_ℂ = ip μ f fun y => L y v

end GlobalTheory.CompanionTheory.WaveK.Base
