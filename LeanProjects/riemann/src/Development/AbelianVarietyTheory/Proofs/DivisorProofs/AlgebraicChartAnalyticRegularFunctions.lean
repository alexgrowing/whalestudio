import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import ReciprocityTheory.SemistableReduction.ShareDetA
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

namespace GlobalTheory

theorem analyticOnNhd_comp_algChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (R : AnRead p σ D) (C : Type) [CommRing C] [Algebra ℂ C] (d' : ℕ) (ι : (C →ₐ[ℂ] ℂ) → CxPts p σ), Continuous ι → (∀ (U : X.Opens) (f : Γ(X, U)) (e : OpenPartialHomeomorph (C →ₐ[ℂ] ℂ) (Fin d' → ℂ)), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (GlobalTheory.CxPts.ev p σ U f ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' GlobalTheory.CxPts.ptsIn p σ U))) → ∀ (O : Set (CxPts p σ)) (g : CxPts p σ → ℂ), IsOpen O → R.HoloOn O g → ∀ e : OpenPartialHomeomorph (C →ₐ[ℂ] ℂ) (Fin d' → ℂ), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (g ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' O)) := by
  intro k _ X p σ D R C _ _ d' ι hι hev O g hO hg e he z hz
  obtain ⟨hzt, hzO⟩ := hz
  obtain ⟨i, hi⟩ := R.cover (ι (e.symm z))
  have hN : e.target ∩ e.symm ⁻¹' (ι ⁻¹' ((R.chart i).e.source ∩ O)) ∈ 𝓝 z :=
    (e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (((R.chart i).e.open_source.inter hO).preimage hι)).mem_nhds ⟨hzt, hi, hzO⟩
  have hcoord : ∀ a, AnalyticAt ℂ
      (fun w => GlobalTheory.CxPts.ev p σ (R.chart i).U ((R.chart i).x a) (ι (e.symm w))) z :=
    fun a => hev (R.chart i).U ((R.chart i).x a) e he z ⟨hzt, (R.chart i).source_subset hi⟩
  have hφ : AnalyticAt ℂ (fun w => (EuclideanSpace.equiv (Fin D) ℂ).symm
      (fun a => GlobalTheory.CxPts.ev p σ (R.chart i).U ((R.chart i).x a) (ι (e.symm w)))) z :=
    ((EuclideanSpace.equiv (Fin D) ℂ).symm.analyticAt _).comp (analyticAt_pi_iff.2 hcoord)
  have hce : ∀ y ∈ (R.chart i).e.source, (EuclideanSpace.equiv (Fin D) ℂ).symm
      (fun a => GlobalTheory.CxPts.ev p σ (R.chart i).U ((R.chart i).x a) y) = (R.chart i).e y := by
    intro y hy
    ext a
    simp [(R.chart i).apply_eq y hy a]
  have hg' : AnalyticAt ℂ (g ∘ (R.chart i).e.symm) ((R.chart i).e (ι (e.symm z))) :=
    ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn (GlobalTheory.ChartGlue.isOpen_over (R.chart i).e hO) (hg i) _
      (GlobalTheory.ChartGlue.mem_over (R.chart i).e hi hzO)
  have hc := hg'.comp_of_eq hφ (hce _ hi)
  refine hc.congr ?_
  filter_upwards [hN] with w hw
  simp only [Function.comp_apply]
  rw [hce _ hw.2.1, (R.chart i).e.left_inv hw.2.1]

end GlobalTheory
