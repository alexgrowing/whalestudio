import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubsetStatement
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDensOff

theorem part_off_sources_eq_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ)
    (ρ : AlgChart p σ D → CxPts p σ → ℝ), part ρ {y | ∀ c : AlgChart p σ D, y ∉ c.e.source} = 0 := by
  intro k _ X p σ D ρ
  set K : Set (CxPts p σ) := ⋃ c : AlgChart p σ D, c.e.source with hKdef
  have hK : MeasurableSet K := (isOpen_iUnion fun c : AlgChart p σ D => c.e.open_source).measurableSet
  have hN : {y | ∀ c : AlgChart p σ D, y ∉ c.e.source} = Kᶜ := by
    ext y
    simp [hKdef]
  rw [hN]
  have key : part ρ ≤ (part ρ).restrict K := iSup_le fun c => by
    have e : ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) Kᶜ = 0 := by
      rw [ChartGlue.chartMeas_apply _ _ hK.compl]
      have h0 : c.e.source ∩ Kᶜ = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
        intro hy
        exact Set.mem_iUnion.2 ⟨c, hy⟩
      rw [h0, Set.image_empty, Measure.restrict_empty, lintegral_zero_measure]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c)
  refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
  rw [Measure.restrict_apply hK.compl, Set.compl_inter_self, measure_empty]

end GlobalTheory.MixDensOff
