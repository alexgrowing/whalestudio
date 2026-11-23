import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensityBoundNearPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLintegralPoissonKernelBoundaryStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineCos

section General

open ReciprocityTheory.L2DbarEstimates (V)

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem reDens_fn_mul (g : M → ℝ) (Φ : A.Fld) (i : A.ι) {z : V n} (hz : z ∈ (A.e i).target) :
    A.reDens (A.fn g * Φ) i z = g ((A.e i).symm z) * A.reDens Φ i z := by
  have h : (A.fn g * Φ) ⟨(i, (A.e i).symm z), (A.e i).map_target hz⟩ =
      ((g ((A.e i).symm z) : ℝ) : ℂ) • Φ ⟨(i, (A.e i).symm z), (A.e i).map_target hz⟩ := by
    rw [Algebra.smul_def]
    rfl
  simp only [HolAtlas.reDens, HolAtlas.loc, dif_pos hz]
  rw [h, dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc, Complex.re_ofReal_mul]
  rfl

theorem part_fn_mul_chart [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (g : M → ℝ) {Φ : A.Fld}
    (hΦ : A.IsForm Φ) (ε : ℤˣ) (i : A.ι) {U : Set (V n)} (hU : IsOpen U) (hUt : U ⊆ (A.e i).target) :
    A.part (A.fn g * Φ) ε ((A.e i).source ∩ A.e i ⁻¹' U) =
      ∫⁻ z in U, ENNReal.ofReal (g ((A.e i).symm z) * (((ε : ℤ) : ℝ) * A.reDens Φ i z)) := by
  have hWm : MeasurableSet ((A.e i).source ∩ A.e i ⁻¹' U) := ((A.e i).isOpen_inter_preimage hU).measurableSet
  have hcompat := A.ofReal_compat (fun i v => ((ε : ℤ) : ℝ) * A.reDens (A.fn g * Φ) i v)
    (fun i j y hi hj => by
      rw [reDens_fn_mul A g Φ i ((A.e i).map_source hi), reDens_fn_mul A g Φ j ((A.e j).map_source hj),
        (A.e i).left_inv hi, (A.e j).left_inv hj, A.reDens_compat hΦ i j y hi hj]
      ring)
  have hp : A.part (A.fn g * Φ) ε = ChartGlue.glueMeas A.e
      (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * A.reDens (A.fn g * Φ) i (A.e i y))) := rfl
  have himg : A.e i '' ((A.e i).source ∩ A.e i ⁻¹' U) = U := by
    ext z
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact hy
    · intro hz
      exact ⟨(A.e i).symm z, ⟨(A.e i).map_target (hUt hz), by simpa [(A.e i).right_inv (hUt hz)] using hz⟩,
        (A.e i).right_inv (hUt hz)⟩
  rw [hp, ChartGlue.glueMeas_apply _ _ A.holo hcompat i hWm Set.inter_subset_left,
    ChartGlue.chartMeas_apply_of_subset (A.e i) _ hWm Set.inter_subset_left, himg]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  simp only [(A.e i).right_inv (hUt hz), reDens_fn_mul A g Φ i (hUt hz)]
  congr 1
  ring

end General

theorem tendsto_integral_kernel_mul : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ Φ : (hY.atlas σ).Fld, (hY.atlas σ).IsForm Φ → (∀ x : (hY.atlas σ).Pt, v x.pt = 1 → dens (Φ x) = 0) →
      Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv Φ hΦ h0
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have main : ∀ ε : ℤˣ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).part
      ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ) ε Set.univ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro ε
    have loc : ∀ y : CxPts p σ, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ Filter.Tendsto (fun t : ℝ => (hY.atlas σ).part
        ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ) ε W) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      intro y
      obtain ⟨c, G, s, O, hy, hO, hcy, hOt, hG, hGp⟩ := GlobalTheory.T.flag_bundle_curvature_at_point k B Y q p d hB hY π w E h H flB fl hfl σ v hv y
      obtain ⟨N, hN, hzN, hNO, C, hC, hle⟩ :=
        GlobalTheory.T.local_density_bound_near_point d O (fun _ => 1) G s (c.e y) hO hcy continuousOn_const hG fun z hz => (hGp z hz).1
      obtain ⟨K, hK, hyK, hKN⟩ := exists_compact_subset hN hzN
      have hF := GlobalTheory.LineCos.continuousOn_cosSq s hG fun z hz => (hGp z hz).1
      have hKO : K ⊆ O := hKN.trans hNO
      have hKt : K ⊆ c.e.target := hKO.trans hOt
      have hle' : Measure.map (fun z => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z))
          (volume.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
        refine le_trans ?_ hle
        simp only [ENNReal.ofReal_one]
        rw [show (fun _ : ReciprocityTheory.L2DbarEstimates.V (d + 1) => (1 : ENNReal)) = 1 from rfl, withDensity_one]
        exact Measure.map_mono_of_aemeasurable (Measure.restrict_mono hKN le_rfl)
          ((hF.mono hNO).aemeasurable hN.measurableSet)
      have hD : ContinuousOn (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens Φ c z) K :=
        (continuousOn_const.mul ((hY.atlas σ).continuousOn_reDens hΦ c)).mono hKt
      have hz0 : ∀ z ∈ K, GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z) = 1 →
          ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens Φ c z = 0 := by
        intro z hz h1
        have hzt : z ∈ ((hY.atlas σ).e c).target := hKt hz
        have := h0 ⟨(c, ((hY.atlas σ).e c).symm z), ((hY.atlas σ).e c).map_target hzt⟩
          (((hGp z (hKO hz)).2).trans h1)
        simp only [HolAtlas.reDens, HolAtlas.loc, dif_pos hzt, this, Complex.zero_re, mul_zero]
      have hlim := GlobalTheory.T.tendsto_lintegral_poisson_kernel_boundary _ volume K _ _ C hK (hF.mono hKO) hD hz0 hC hle'
      refine ⟨((hY.atlas σ).e c).source ∩ (hY.atlas σ).e c ⁻¹' interior K,
        ((hY.atlas σ).e c).isOpen_inter_preimage isOpen_interior, ⟨hy, hyK⟩, ?_⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => zero_le) fun t => ?_
      beta_reduce
      rw [part_fn_mul_chart (hY.atlas σ) _ hΦ ε c isOpen_interior (interior_subset.trans hKt)]
      refine le_trans (le_of_eq ?_) (lintegral_mono_set interior_subset)
      refine setLIntegral_congr_fun isOpen_interior.measurableSet fun z hz => ?_
      have := (hGp z (hKO (interior_subset hz))).2
      beta_reduce
      rw [← this]
      rfl
    choose W hWo hyW hW using loc
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩
    have hs := tendsto_finset_sum T fun y _ => hW y
    rw [Finset.sum_const_zero] at hs
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun t => zero_le)
      fun t => (measure_mono hT).trans (measure_biUnion_finset_le T _)
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (main 1)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (main (-1))
  have := h1.sub h2
  rw [ENNReal.toReal_zero, sub_zero] at this
  exact this

end GlobalTheory.LineCos
