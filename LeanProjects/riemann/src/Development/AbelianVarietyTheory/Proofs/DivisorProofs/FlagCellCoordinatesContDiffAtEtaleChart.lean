import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegular

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

open GlobalTheory.Points GlobalTheory.ChartGlue

theorem contDiffAt_chart_of_eqOn_ev {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {D : ℕ} (c' : AlgChart Y.str σ D)
    {g : CxPts Y.str σ → ℂ} {S : Set (CxPts Y.str σ)} (hS : IsOpen S) {W : Y.X.Opens} (a : Γ(Y.X, W))
    (hg : ∀ z ∈ S, g z = ev Y.str σ W a z) {y : CxPts Y.str σ} (hy : y ∈ c'.e.source) (hyS : y ∈ S)
    (hyW : y ∈ ptsIn Y.str σ W) : ContDiffAt ℂ 2 (g ∘ c'.e.symm) (c'.e y) := by
  have hO := isOpen_over c'.e (hS.inter (isOpen_ptsIn (p := Y.str) (σ := σ) W))
  have hm := mem_over c'.e (S := S ∩ ptsIn Y.str σ W) hy ⟨hyS, hyW⟩
  have hd : DifferentiableOn ℂ (ev Y.str σ W a ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (S ∩ ptsIn Y.str σ W)) :=
    (c'.holo W a).mono fun v hv => ⟨hv.1, hv.2.2⟩
  have h1 : ContDiffAt ℂ 2 (ev Y.str σ W a ∘ c'.e.symm) (c'.e y) := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ hO hd).contDiffAt (hO.mem_nhds hm)).of_le
    (by norm_cast)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hm] with v hv
  exact hg _ hv.2.1

theorem cellMap_contDiffAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ x.ch.symm) x.crd := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε x hx
  obtain ⟨hcell, hsrc⟩ := hx
  have hreg := (isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).2 _ hcell
  set c' : AlgChart Y.str σ Y.dim := x.1.1
  have hy : x.pt ∈ c'.e.source := x.2
  change ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ c'.e.symm) (c'.e x.pt)
  refine contDiffAt_euclidean.2 fun a => ?_
  change ContDiffAt ℂ 2 ((fun z => cellMap ε f hf c u z a) ∘ c'.e.symm) (c'.e x.pt)
  rcases hε : ε a with b | j
  · have hS : IsOpen (ptMap σ f hf ⁻¹' c.e.source) :=
      c.e.open_source.preimage (PtsOver.continuous_map f hf _)
    refine contDiffAt_chart_of_eqOn_ev c' hS (f.app c.U (c.x b)) (fun z hz => ?_) hy hsrc ?_
    · simp only [cellMap, pt, hε, Sum.elim_inl]
      rw [c.apply_eq _ hz b, ev_app f hf]
      rfl
    · rw [mem_ptsIn]
      exact mem_ptsIn.1 (c.source_subset hsrc)
  · obtain ⟨U, hU, w, hw⟩ := (hreg j).exists_fnOf
    refine contDiffAt_chart_of_eqOn_ev c' (isOpen_ptsIn U) w (fun z hz => ?_) hy (mem_ptsIn.2 hU) (mem_ptsIn.2 hU)
    simp only [cellMap, pt, hε, Sum.elim_inr]
    rw [← hw, ratVal_fnOf hz]

end GlobalTheory.FlagCell2
