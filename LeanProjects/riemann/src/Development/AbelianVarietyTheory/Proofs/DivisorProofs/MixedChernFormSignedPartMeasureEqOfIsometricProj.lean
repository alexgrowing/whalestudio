import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open ReciprocityTheory.L2DbarEstimates (V cHess)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem MLine.Isom.hess_eq {L M : MLine p σ} (h : L.Isom M) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) {a : M.B.ι} {b : L.B.ι} (ha : y ∈ ptsIn p σ (M.B.U a)) (hb : y ∈ ptsIn p σ (L.B.U b)) :
    c.hess M.φ a y = c.hess L.φ b y := by
  obtain ⟨w, -, h⟩ := h
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (M.B.U a ⊓ L.B.U b),
      (ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 :=
    fun v hv => ev_ne_zero hv.2 (w.s _).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (L.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [h _ _ _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem dens_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) : dens L c y = dens M c y := by
  have e (i : Fin D) := (h i).hess_eq c hy (mem_pick (M i).φ.isLB y) (mem_pick (L i).φ.isLB y)
  simp only [dens, e]

theorem part_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (ε : ℤˣ) :
    part L ε = part M ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun ?_ ?_
  · exact measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) inter_subset_left
  · rintro _ ⟨y, hy, rfl⟩
    simp only [c.e.left_inv hy.1, dens_congr_isom h c hy.1]

theorem part_eq_of_isom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε :=
  fun _ _ _ _ _ _ _ _ _ h ε => part_congr_isom h ε

end GlobalTheory.Mix
