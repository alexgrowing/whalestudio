import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulesIsoOfMatchingFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

namespace GlobalTheory.FlagCell

theorem steps_iso_of_spans_top : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl₁ fl₂ : Vert.Flag F m) (v : Fin m → Γ(F, ⊤)), Spans fl₁ ⊤ v → Spans fl₂ ⊤ v → ∀ i, ∃ e : fl₁.F i ≅ fl₂.F i, e.hom ≫ fl₂.ι i = fl₁.ι i := by
  intro X F m fl₁ fl₂ v h₁ h₂ i
  obtain ⟨s₁, hs₁, e₁⟩ := h₁ i
  obtain ⟨s₂, hs₂, e₂⟩ := h₂ i
  exact GlobalTheory.VB.exists_iso_of_frames_app_eq (fl₁.ι i) (fl₂.ι i) (i : ℕ)
    fun _ => ⟨⊤, s₁, s₂, trivial, hs₁, hs₂, fun j => (e₁ j).trans (e₂ j).symm⟩

end GlobalTheory.FlagCell
