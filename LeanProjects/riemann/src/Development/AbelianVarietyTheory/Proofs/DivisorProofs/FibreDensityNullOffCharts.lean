import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubset
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
noncomputable section

namespace GlobalTheory.ChartFibreNull

theorem part_preimage_nonchart : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n D : ℕ) (σ : k →+* ℂ) [IsIntegral B] [IsIntegral Y], IsArithVar q n → IsArithVar p D → π (genericPoint Y) = genericPoint B → ∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, part ρ (PtsOver.map π w (spMap σ) ⁻¹' {u | ∀ c : AlgChart q σ n, u ∉ c.e.source}) = 0 := by
  intro k _ B Y q p π w n D σ _ _ hq hp hgen ρ
  obtain ⟨T, hT, hTgen, hch⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k B q n hq
  refine measure_mono_null ?_ (GlobalTheory.MixDensNull.part_over_closed k Y p D hp (π ⁻¹' T)
    (hT.preimage π.continuous) (by simpa [hgen] using hTgen) σ ρ)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy ⊢
  by_contra hnot
  obtain ⟨c, hc⟩ := hch σ (PtsOver.map π w (spMap σ) y) hnot
  exact hy c hc

end GlobalTheory.ChartFibreNull
