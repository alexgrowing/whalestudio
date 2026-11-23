import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
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
open GlobalTheory.IrrAn
open scoped GlobalTheory.AffinePoints

namespace GlobalTheory.IrrAn

theorem preconnected_locIdent_range_of_algebraicCharts : ∀ (d : ℕ) (Y : Type) [TopologicalSpace Y] (A : FinHolAtlas d Y) (C : Type) [CommRing C] [IsDomain C] [Algebra ℂ C] [Algebra.FiniteType ℂ C] (d' : ℕ) (ι : (C →ₐ[ℂ] ℂ) → Y), GlobalTheory.AffinePoints.HasAlgebraicCharts ℂ C d' → Topology.IsEmbedding ι → (∀ (O : Set Y) (g : Y → ℂ), IsOpen O → A.HoloOn O g → ∀ e : OpenPartialHomeomorph (C →ₐ[ℂ] ℂ) (Fin d' → ℂ), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (g ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' O))) → IsPreconnected (Set.range ι) ∧ GlobalTheory.IrrAn.LocIdent A (Set.range ι) := by
  intro d Y _ A C _ _ _ _ d' ι hch hι hana
  have hpc : PreconnectedSpace (C →ₐ[ℂ] ℂ) := GlobalTheory.RootConst.preconnectedSpace_algHom C
  refine ⟨isPreconnected_range hι.continuous, ?_⟩
  rintro x ⟨φ, rfl⟩ W hW hxW
  obtain ⟨e, he, hφ⟩ := hch φ
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' (ι ⁻¹' W)) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target (hW.preimage hι.continuous)
  have hmem : e φ ∈ e.target ∩ e.symm ⁻¹' (ι ⁻¹' W) :=
    ⟨e.map_source hφ, by simpa [e.left_inv hφ] using hxW⟩
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hopen (e φ) hmem
  set B := Metric.ball (e φ) r with hBdef
  have hBt : B ⊆ e.target := fun z hz => (hB hz).1
  have hBo : IsOpen (e.symm '' B) :=
    e.symm.isOpen_image_of_subset_source Metric.isOpen_ball (by simpa using hBt)
  obtain ⟨N', hN'o, hN'⟩ := hι.isInducing.isOpen_iff.1 hBo
  refine ⟨N' ∩ W, hN'o.inter hW, ⟨?_, hxW⟩, Set.inter_subset_right, ?_⟩
  · show φ ∈ ι ⁻¹' N'
    rw [hN']
    exact ⟨e φ, Metric.mem_ball_self hr, e.left_inv hφ⟩
  rintro g hg x' ⟨⟨ψ, rfl⟩, hψN, -⟩ hev y ⟨⟨χ, rfl⟩, hχN, -⟩
  have hψ : ψ ∈ e.symm '' B := by rw [← hN']; exact hψN
  have hχ : χ ∈ e.symm '' B := by rw [← hN']; exact hχN
  obtain ⟨b, hb, rfl⟩ := hψ
  obtain ⟨b', hb', rfl⟩ := hχ
  have han : AnalyticOnNhd ℂ (g ∘ ι ∘ e.symm) B :=
    fun z hz => hana W g hW hg e he z (hB hz)
  have hca : ContinuousAt (ι ∘ e.symm) b :=
    hι.continuous.continuousAt.comp (e.continuousAt_symm (hBt hb))
  have hz : (g ∘ ι ∘ e.symm) =ᶠ[𝓝 b] 0 := by
    filter_upwards [hca.eventually hev] with z hz
    exact hz ⟨_, rfl⟩
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (e φ) r).isPreconnected hb hz hb'
  simpa using this

end GlobalTheory.IrrAn
