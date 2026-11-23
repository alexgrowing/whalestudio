import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLiftAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

noncomputable section

theorem GlobalTheory.MixDens.exists_cell_charts : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (c₀ : AlgChart q σ 1), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ 1) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ (d + 1)), y ∈ c.e.source ∧ (∀ a, c.e.source ⊆ ptsIn q σ (cE a).U) ∧ IsCell e π w c c' ∧ ∀ a, IsCellFrame e π w c' a (h a) (fl a) (cE a) := by
  intro k _ B Y q p π w ι _ r d e σ E h fl hfl c₀ y hy
  have hx : ∀ a, ∃ (U : B.Opens) (f : Fin (r a) → Γ(E a, U)), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ IsFrame f :=
    fun a => (h a).isVB _
  choose U f hxU hf using hx
  let V : B.Opens := Finset.univ.inf U
  have hV (a : ι) : V ≤ U a := Finset.inf_le (Finset.mem_univ a)
  have hyV : y ∈ ptsIn q σ V := by
    rw [mem_ptsIn]
    show _ ∈ ((Finset.univ.inf U : B.Opens) : Set B)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simpa using hxU
  obtain ⟨c, hyc, hcV⟩ := GlobalTheory.ChartShrink.exists_chart_le k B q σ c₀ y hy V hyV
  let cE : ∀ a, Chart (E a) (r a) := fun a => ⟨c.U, fun l => GlobalTheory.Twist.resM (E a) (hcV.trans (hV a)) (f a l),
    (hf a).res (hcV.trans (hV a))⟩
  obtain ⟨W, hW, hWa, n, hb, hs⟩ := GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π ι r E fl hfl (fun a => (h a).isVB) c.U c.affine
    (fun a => (cE a).e) fun a => (cE a).isFrame
  obtain ⟨c', hcell, hsrc, hfib⟩ := GlobalTheory.T.exists_isCell_chart_of_bijective_eval₂ k B Y q p π w ι r d e σ c W hW hWa n hb ⟨y, hyc⟩
  refine ⟨c, cE, c', hyc, fun a => c.source_subset, hcell, fun a => ?_⟩
  exact GlobalTheory.FlagCell.isCellFrame_of_spans k B Y q p π w ι r d e σ a (E a) (h a) (fl a) (cE a) c' W hW (fun s => n ⟨a, s⟩) (hs a) hsrc
    fun y hy s => hfib y hy a s
