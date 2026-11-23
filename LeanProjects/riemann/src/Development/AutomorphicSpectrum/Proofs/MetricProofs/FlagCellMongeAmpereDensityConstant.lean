import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvarianceStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cmp

variable {Ψ : Type} [Fintype Ψ] {N e : ℕ}

def stepFam (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) (w : Fin e → Ψ × Fin N) (i : Fin e) (z : Fin e → ℂ) : ℝ :=
  stepPot N j (w i).2 (lowMat q z (w i).1)

def IsReAn (z₀ : Fin e → ℂ) (h : (Fin e → ℂ) → ℝ) : Prop :=
  ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G z₀ ∧ h =ᶠ[𝓝 z₀] fun z => (G z).re

theorem IsReAn.add {z₀ : Fin e → ℂ} {f g : (Fin e → ℂ) → ℝ} (hf : IsReAn z₀ f) (hg : IsReAn z₀ g) :
    IsReAn z₀ (fun z => f z + g z) := by
  obtain ⟨F, hF, h1⟩ := hf
  obtain ⟨G, hG, h2⟩ := hg
  refine ⟨fun z => F z + G z, hF.add hG, ?_⟩
  filter_upwards [h1, h2] with z a b
  simp [a, b]

theorem IsReAn.sub {z₀ : Fin e → ℂ} {f g : (Fin e → ℂ) → ℝ} (hf : IsReAn z₀ f) (hg : IsReAn z₀ g) :
    IsReAn z₀ (fun z => f z - g z) := by
  obtain ⟨F, hF, h1⟩ := hf
  obtain ⟨G, hG, h2⟩ := hg
  refine ⟨fun z => F z - G z, hF.sub hG, ?_⟩
  filter_upwards [h1, h2] with z a b
  simp [a, b]

theorem IsReAn.zero (z₀ : Fin e → ℂ) : IsReAn z₀ (fun _ => 0) :=
  ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun _ => by simp⟩

theorem IsReAn.congr {z₀ : Fin e → ℂ} {f g : (Fin e → ℂ) → ℝ} (hf : IsReAn z₀ f) (h : g =ᶠ[𝓝 z₀] f) :
    IsReAn z₀ g := by
  obtain ⟨F, hF, h1⟩ := hf
  exact ⟨F, hF, h.trans h1⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
