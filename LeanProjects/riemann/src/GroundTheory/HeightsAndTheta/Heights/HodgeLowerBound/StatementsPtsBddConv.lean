import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsPtsNull (P : Ideal (MRing ι)) (e : ℕ) (N : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} = 0

def IsPtsIntegrable (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w)

def PtsBddConv.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : HermLine ι) (r : ℝ) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ) (g₀ : ((Σ k, ι k) → ℂ) → ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (C s₀ : ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → 0 < r → IsPtsNull P e N → 0 < s₀ →
    (∀ s : ℝ, 0 < s → s < s₀ → (∀ z ∈ mcPts P, |g s z| ≤ C) ∧ ContinuousOn (g s) (mcPts P \ N) ∧
      ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, g s (torusSmul c z) = g s z) →
    (∀ z ∈ mcPts P, z ∉ N → Tendsto (fun s => g s z) (𝓝[>] 0) (𝓝 (g₀ z))) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ ∧
      Tendsto (fun s => ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀))

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
