import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDensityChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChartBaseProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBigCellFibreStatement
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

namespace GlobalTheory.FubCell

theorem measurableSet_image_chart {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] [MeasurableSpace X]
    [MeasurableSpace Z] [BorelSpace X] [BorelSpace Z] (e : OpenPartialHomeomorph X Z) {A : Set X}
    (hA : MeasurableSet A) (hs : A ⊆ e.source) : MeasurableSet (e '' A) := by
  rw [e.image_eq_target_inter_inv_preimage hs]
  have h1 : Measurable (e.target.restrict e.symm) := e.continuousOn_symm.restrict.measurable
  have h2 := (MeasurableEmbedding.subtype_coe e.open_target.measurableSet).measurableSet_image.2 (h1 hA)
  convert h2 using 1
  ext v
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.restrict_apply]
  constructor
  · rintro ⟨h3, h4⟩
    exact ⟨⟨v, h3⟩, h4, rfl⟩
  · rintro ⟨⟨u, hu⟩, h4, rfl⟩
    exact ⟨hu, h4⟩

theorem continuous_base {n r D : ℕ} (ε : Fin D ≃ Fin n ⊕ Low r) : Continuous (base ε : V D → V n) := by
  unfold base
  fun_prop

theorem lintegral_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) [IsIntegral Y] (c : AlgChart q σ n) (c' : AlgChart p σ D), IsArithVar p D → IsCell ε π w c c' → ∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, IsDens ρ → ∀ A : Set (CxPts q σ), MeasurableSet A → A ⊆ c.e.source → ∀ h : CxPts q σ → ℝ≥0∞, Measurable h → (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, h (PtsOver.map π w (spMap σ) y) ∂part ρ = ∫⁻ u in c.e '' A, ∫⁻ x : Low r → ℂ, h (c.e.symm u) * ENNReal.ofReal (ρ c' (c'.e.symm (pt ε u x)))) ∧ AEMeasurable (fun u => ∫⁻ x : Low r → ℂ, h (c.e.symm u) * ENNReal.ofReal (ρ c' (c'.e.symm (pt ε u x)))) (volume.restrict (c.e '' A)) := by
  intro k _ B Y q p π w n r D ε σ _ c c' hp hc ρ hρ A hA hAs h hh
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp.isProjOver
  have hmap : Measurable (PtsOver.map π w (spMap σ)) := (PtsOver.continuous_map π w (spMap σ)).measurable
  have hne : c'.e.source.Nonempty := by
    refine ⟨c'.e.symm (pt ε (c.e a) 0), c'.e.map_target ?_⟩
    rw [hc.2.1]
    simpa [base_pt] using c.e.map_source (hAs ha)
  have hnull := GlobalTheory.MixDens.part_compl_ptsIn hp ρ c' hne
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.cell_chart_base_projection k B Y q p π w n r D ε σ c c' hc
  have hK : MeasurableSet (c.e '' A) := measurableSet_image_chart c.e hA hAs
  have hKt : c.e '' A ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hAs hy)
  have hS : MeasurableSet (base ε ⁻¹' (c.e '' A) : Set (V D)) := (continuous_base ε).measurable hK
  have hSt : base ε ⁻¹' (c.e '' A) ⊆ c'.e.target := by
    rw [hc.2.1]
    exact fun v hv => hKt hv
  have hae : (PtsOver.map π w (spMap σ) ⁻¹' A : Set (CxPts p σ)) =ᵐ[part ρ]
      (PtsOver.map π w (spMap σ) ⁻¹' A ∩ c'.e.source : Set (CxPts p σ)) := by
    have : ∀ᵐ y ∂part ρ, y ∈ ptsIn p σ c'.U := hnull
    filter_upwards [this] with y hy
    apply propext
    constructor
    · intro hy'
      refine ⟨hy', ?_⟩
      rw [hc.1]
      exact ⟨hAs hy', hy⟩
    · exact fun hy' => hy'.1
  have hH : AEMeasurable (fun v : V D => h (c.e.symm (base ε v)) * ENNReal.ofReal (ρ c' (c'.e.symm v)))
      (volume.restrict (base ε ⁻¹' (c.e '' A))) := by
    refine AEMeasurable.mul (hh.comp_aemeasurable ?_) (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
    · exact (c.e.continuousOn_symm.comp (continuous_base ε).continuousOn fun v hv => hKt hv).aemeasurable hS
    · exact ((hρ.2 c').mono hSt).aemeasurable hS
  obtain ⟨ht1, ht2⟩ := GlobalTheory.T.lintegral_big_cell_fibre n r D ε (c.e '' A) _ hK hH
  simp only [base_pt] at ht1 ht2
  refine ⟨?_, ht2⟩
  rw [Measure.restrict_congr_set hae,
    GlobalTheory.T.lintegral_density_chart k Y p σ D ρ hρ c' _ ((hmap hA).inter c'.e.open_source.measurableSet) Set.inter_subset_right
      (fun y => h (PtsOver.map π w (spMap σ) y)) (hh.comp hmap), hg2 A hAs, ← ht1]
  refine setLIntegral_congr_fun hS fun v hv => ?_
  simp only [hg1 v (hSt hv)]

end GlobalTheory.FubCell
