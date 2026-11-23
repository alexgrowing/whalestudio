import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem cInfAt_sheet_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (f : CxPts t τ → ℝ) (y : CxPts p σ), CInfAt f (sheet t τ y) ↔ CInfAt (fun z : CxPts p σ => f (sheet t τ z)) y := by
  intro k _ _ X p t τ σ f y
  have hE := (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  constructor
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, hE.continuous.continuousAt.eventually h₅⟩
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, ?_⟩
    show ∀ᶠ w in 𝓝 (sheet t τ y), f w = F fun a => ev t τ W (g a) w
    rw [← hE.map_nhds_eq, eventually_map]
    exact h₅

end GlobalTheory.CompanionTheory.Ar.BaseZ
