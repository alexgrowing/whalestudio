import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcIntegrationByParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLemmaMollifiedHarmonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackFormLocalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStandardVolumeFormProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLaplacianLocalFormulaSphereStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcVanishesOffSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPullbackFunctionFamilyAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralProductFubiniComplexLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFibreIntegralCutoffStatement

set_option autoImplicit false

open Set MeasureTheory Filter
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique

theorem const_of_weakly_harmonic (u : OnePoint ℂ → ℝ) (hu : Continuous u)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ w : ℂ, u w * Laplacian.laplacian φ w = 0)
    (t t' : OnePoint ℂ) : u t = u t' := by
  have hg : Continuous fun w : ℂ => u w := hu.comp OnePoint.continuous_coe
  obtain ⟨C, hC⟩ := (isCompact_range hu).isBounded.exists_norm_le
  let b : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc (n : ℕ) := InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant _
    (GlobalTheory.T.weyl_lemma_mollified_harmonic _ hg h ((b n).normed volume) (b n).contDiff_normed (b n).hasCompactSupport_normed) (by
      refine isBounded_iff_forall_norm_le.2 ⟨∫ s, ‖(b n).normed volume s‖ * C, ?_⟩
      rintro _ ⟨x, rfl⟩
      refine norm_integral_le_of_norm_le ((b n).integrable_normed.norm.mul_const C) (.of_forall fun s => ?_)
      rw [ContinuousLinearMap.lsmul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left (hC _ ⟨_, rfl⟩) (norm_nonneg _))
  have h0 (z : ℂ) : u z = u (0 : ℂ) :=
    tendsto_nhds_unique (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hb hg z)
      ((ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hb hg 0).congr fun n => hc n 0 z)
  have e : u = fun _ => u (0 : ℂ) :=
    Continuous.ext_on OnePoint.denseRange_coe hu continuous_const (by rintro _ ⟨z, rfl⟩; exact h0 z)
  rw [congrFun e t, congrFun e t']

theorem integrable_dens_loc {X : Type} [TopologicalSpace X] {n : ℕ} (B : HolAtlas X n) {η : B.Fld} (hη : B.IsForm η)
    (i : B.ι) {K : Set X} (hK : IsCompact K) (hKs : K ⊆ (B.e i).source) (h0 : ∀ x : B.Pt, x.pt ∉ K → η x = 0) :
    Integrable fun v => (dens (B.loc η i v)).re := by
  have hBc : IsCompact (B.e i '' K) := hK.image_of_continuousOn ((B.e i).continuousOn.mono hKs)
  have hBt : B.e i '' K ⊆ (B.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (B.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ B.e i '' K, (dens (B.loc η i v)).re = 0 := by
    intro v hv
    by_cases ht : v ∈ (B.e i).target
    · have e : B.loc η i v = 0 := (dif_pos ht).trans
        (h0 ⟨(i, (B.e i).symm v), (B.e i).map_target ht⟩ fun hk => hv ⟨_, hk, (B.e i).right_inv ht⟩)
      simp [e, dens]
    · simp [HolAtlas.loc, ht, dens]
  have hcon : ContinuousOn (fun v => (dens (B.loc η i v)).re) (B.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hη.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous fun v => (dens (B.loc η i v)).re := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (B.e i).target
    · exact hcon.continuousAt ((B.e i).open_target.mem_nhds ht)
    · have : (fun v => (dens (B.loc η i v)).re) =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  exact hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)

theorem dens_real_smul {n : ℕ} (c : ℝ) (a : Alt n) : (dens ((c : ℂ) • a)).re = c * (dens a).re := by
  rw [← Complex.re_ofReal_mul, dens, dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem loc_fn_mul {X : Type} [TopologicalSpace X] {n : ℕ} (B : HolAtlas X n) (g : X → ℝ) (η : B.Fld) (i : B.ι)
    (v : V n) : B.loc (B.fn g * η) i v = (g ((B.e i).symm v) : ℂ) • B.loc η i v := by
  unfold HolAtlas.loc
  split_ifs
  · rw [Algebra.smul_def]
    rfl
  · exact (smul_zero _).symm

theorem eq_sum_fn_mul {X : Type} [TopologicalSpace X] {n N : ℕ} (B : HolAtlas X n) (χ : Fin N → X → ℝ)
    (h1 : ∀ y, ∑ j, χ j y = 1) (η : B.Fld) : η = ∑ j, B.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  funext x
  simp only [Finset.sum_apply, Pi.mul_apply, HolAtlas.fn, ← map_sum]
  rw [show (∑ j, ((χ j x.pt : ℝ) : ℂ)) = 1 by exact_mod_cast h1 x.pt, map_one, one_mul]

section Fam

variable {M : Type} [TopologicalSpace M] (A : HolAtlas M 1)

theorem dens_loc_prod {γ : (famAtlas A).Fld} (hγ : (famAtlas A).IsForm γ) (χ : M → ℝ) (j : A.ι) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : V 1) (w : ℂ) :
    (dens ((famAtlas A).loc ((famAtlas A).fn (fun y => χ y.1) *
      ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) * γ)) (j, sphFin)
        (appendV 1 1 (v, EuclideanSpace.single 0 w)))).re =
      (dens (A.loc (A.fn χ * (famAtlas A).pullback A (fib (w : OnePoint ℂ)) γ) j v)).re *
        (Laplacian.laplacian φ w / (4 * π)) := by
  have e1 := loc_fn_mul (famAtlas A) (fun y => χ y.1)
    ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) * γ) (j, sphFin)
    (appendV 1 1 (v, EuclideanSpace.single 0 w))
  have e2 := congrFun (ByParts.loc_mul (famAtlas A) ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ)) γ
    (j, sphFin)) (appendV 1 1 (v, EuclideanSpace.single 0 w))
  have e3 := GlobalTheory.T.fibre_pullback_form_local_coordinates M A γ hγ j sphFin w ⟨w, rfl⟩ v
  rw [sphFin_apply] at e3
  rw [famAtlas_symm_appendV] at e1
  rw [e1, loc_fn_mul, dens_real_smul, dens_real_smul, e3, ← GlobalTheory.T.density_standard_volume_form_product, e2]
  by_cases hv : appendV 1 1 (v, EuclideanSpace.single 0 w) ∈ ((famAtlas A).e (j, sphFin)).target
  · rw [GlobalTheory.T.ddc_laplacian_local_formula_sphere M A φ hφ j _ hv, smul_mul_assoc, dens_real_smul, appendV_last]
    simp only [PiLp.single_apply, if_true]
    ring
  · have e4 : (famAtlas A).loc γ (j, sphFin) (appendV 1 1 (v, EuclideanSpace.single 0 w)) = 0 := dif_neg hv
    simp [e4, dens]

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem integral_fn_mul_ddc_mul [MeasurableSpace (M × OnePoint ℂ)] [BorelSpace (M × OnePoint ℂ)]
    {γ : (famAtlas A).Fld} (hγ : (famAtlas A).IsForm γ) {χ : M → ℝ} {j : A.ι}
    (hχ : A.SmoothOn univ fun y => (χ y : ℂ)) (hs : tsupport χ ⊆ (A.e j).source) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (famAtlas A).integral ((famAtlas A).fn (fun y => χ y.1) *
      ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) * γ)) =
      ∫ w : ℂ, A.integral (A.fn χ * (famAtlas A).pullback A (fib (w : OnePoint ℂ)) γ) *
        (Laplacian.laplacian φ w / (4 * π)) := by
  obtain ⟨-, C, -, -, P⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (famAtlas A)
  obtain ⟨-, C', -, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ A
  have hG := (famAtlas A).isForm_fn (GlobalTheory.T.smooth_pullback_function_family_atlas M A φ hφ hc)
  have h1 := (C 0 _ _ hG hG).2.2.2.2.1
  have h2 := (C 0 _ _ h1 h1).2.2.2.1
  have h3 : (famAtlas A).IsForm ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ)) :=
    (C HermFrame.kappa _ _ h2 h2).2.2.1
  have h4 := (C 0 _ _ ((famAtlas A).isForm_fn (u := fun y => χ y.1) (smoothOn_fst A hχ)) (C 0 _ _ h3 hγ).2.1).2.1
  have hKχ : IsCompact (tsupport χ) := (isClosed_tsupport χ).isCompact
  have hK : IsCompact (tsupport χ ×ˢ (((↑) : ℂ → OnePoint ℂ) '' tsupport φ)) :=
    hKχ.prod (hc.isCompact.image OnePoint.continuous_coe)
  have hKs : tsupport χ ×ˢ (((↑) : ℂ → OnePoint ℂ) '' tsupport φ) ⊆ ((famAtlas A).e (j, sphFin)).source :=
    prod_mono hs (image_subset_range _ _)
  have h0 : ∀ x : (famAtlas A).Pt, x.pt ∉ tsupport χ ×ˢ (((↑) : ℂ → OnePoint ℂ) '' tsupport φ) →
      ((famAtlas A).fn (fun y => χ y.1) * ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) * γ)) x = 0 := by
    intro x hx
    rw [Pi.mul_apply, Pi.mul_apply]
    rcases not_and_or.1 hx with h | h
    · simp [HolAtlas.fn, image_eq_zero_of_notMem_tsupport h]
    · rw [GlobalTheory.T.ddc_vanishes_off_support M A φ hc x h, zero_mul, mul_zero]
  have e1 := HolAtlas.integral_eq_integral_chart_of_support (famAtlas A) _ (j, sphFin) _ h4 hK hKs h0
  have e2 := GlobalTheory.T.integral_product_fubini_complex_line _ (integrable_dens_loc (famAtlas A) h4 (j, sphFin) hK hKs h0)
  refine (e1.trans e2).trans (integral_congr_ae (.of_forall fun w => ?_))
  have h5 := (((P M 1 A _ (isHolo_fib A w)).2 0 γ γ).2.2.2 hγ).1
  simp only []
  rw [HolAtlas.integral_eq_integral_chart_of_support A _ j _ (C' 0 _ _ (A.isForm_fn hχ) h5).2.1 hKχ hs
    (fun x hx => by simp [HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]), ← integral_mul_const]
  exact integral_congr_ae (.of_forall fun v => dens_loc_prod A hγ χ j hφ v w)

theorem integral_fib_eq_of_ddc_eq_zero {γ : (famAtlas A).Fld} (hγ : (famAtlas A).IsForm γ)
    (hd : (famAtlas A).ddc γ = 0) (t t' : OnePoint ℂ) :
    A.integral ((famAtlas A).pullback A (fib t) γ) = A.integral ((famAtlas A).pullback A (fib t') γ) := by
  obtain ⟨hone, C, -, -, P⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (famAtlas A)
  obtain ⟨-, C', -, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ A
  obtain ⟨N, c, χ, hχ, hs, h1⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hsum (t : OnePoint ℂ) : A.integral ((famAtlas A).pullback A (fib t) γ) =
      ∑ j, A.integral (A.fn (χ j) * (famAtlas A).pullback A (fib t) γ) := by
    rw [← GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ fun j =>
      (C' 0 _ _ (A.isForm_fn (hχ j)) (((P M 1 A _ (isHolo_fib A t)).2 0 γ γ).2.2.2 hγ).1).2.1, ← eq_sum_fn_mul A χ h1]
  have hcj (j : Fin N) := GlobalTheory.T.continuous_fibre_integral_cutoff M A γ hγ (χ j) (c j) (hχ j) (hs j)
  refine const_of_weakly_harmonic (fun t => A.integral ((famAtlas A).pullback A (fib t) γ)) ?_ ?_ t t'
  · simp only [hsum]
    exact continuous_finset_sum _ fun j _ => hcj j
  intro φ hφ hc
  letI : MeasurableSpace (M × OnePoint ℂ) := borel _
  haveI : BorelSpace (M × OnePoint ℂ) := ⟨rfl⟩
  have hGs := GlobalTheory.T.smooth_pullback_function_family_atlas M A φ hφ hc
  have hG := (famAtlas A).isForm_fn hGs
  have h2 := (C 0 _ _ hG hG).2.2.2.2.1
  have h3 := (C 0 _ _ h2 h2).2.2.2.1
  have h4 : (famAtlas A).IsForm ((famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) * γ) :=
    (C 0 _ _ (C HermFrame.kappa _ _ h3 h3).2.2.1 hγ).2.1
  have hz : (famAtlas A).integral 0 = 0 := by
    have := HolAtlas.integral_sub_of_isForm (famAtlas A) _ _ hone hone
    rwa [sub_self, sub_self] at this
  have key := ByParts.integral_fn_mul_ddc _ _ (famAtlas A) _ hGs γ hγ
  rw [hd, mul_zero, hz, eq_sum_fn_mul (famAtlas A) (fun j y => χ j y.1) (fun y => h1 y.1) (_ * γ),
    GlobalTheory.T.holAtlas_integral_fin_sum_compact _ _ fun j => (C 0 _ _ ((famAtlas A).isForm_fn (u := fun y => χ j y.1) (smoothOn_fst A (hχ j))) h4).2.1,
    Finset.sum_congr rfl fun j _ => integral_fn_mul_ddc_mul A hγ (hχ j) (hs j) hφ hc] at key
  have hD : Continuous (iteratedFDeriv ℝ 2 φ) :=
    hφ.continuous_iteratedFDeriv (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hlc : Continuous fun w => Laplacian.laplacian φ w / (4 * π) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    fun_prop
  have hls : HasCompactSupport fun w => Laplacian.laplacian φ w / (4 * π) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    exact (hc.iteratedFDeriv (𝕜 := ℝ) 2).mono fun w hw h => hw (by simp [h])
  have hint (j : Fin N) : Integrable fun w : ℂ =>
      A.integral (A.fn (χ j) * (famAtlas A).pullback A (fib (w : OnePoint ℂ)) γ) * (Laplacian.laplacian φ w / (4 * π)) :=
    (((hcj j).comp OnePoint.continuous_coe).mul hlc).integrable_of_hasCompactSupport hls.mul_left
  rw [← integral_finset_sum _ fun j _ => hint j] at key
  simp only [← Finset.sum_mul, ← hsum] at key
  simp only [← mul_div_assoc, integral_div] at key
  exact (div_eq_zero_iff.1 key.symm).resolve_right (by positivity)

end Fam

theorem integral_fib_add_const : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M 1) (α β : (famAtlas A).Fld), (famAtlas A).IsRealForm 1 α → (famAtlas A).IsRealForm 1 β → (∀ x, (famAtlas A).ddc α x + (famAtlas A).ddc β x = 0) → ∀ t t' : OnePoint ℂ, A.integral ((famAtlas A).pullback A (fib t) α) + A.integral ((famAtlas A).pullback A (fib t) β) = A.integral ((famAtlas A).pullback A (fib t') α) + A.integral ((famAtlas A).pullback A (fib t') β) := by
  intro M _ _ _ _ _ _ A α β hα hβ hd t t'
  obtain ⟨-, C, -, -, P⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (famAtlas A)
  obtain ⟨-, C', -, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ A
  have h1 := C 0 _ _ hα.1 hβ.1
  have h2 := C 0 _ _ h1.2.2.2.2.1 (C 0 _ _ hβ.1 hβ.1).2.2.2.2.1
  have hd' : (famAtlas A).ddc (α + β) = 0 := by
    rw [HolAtlas.ddc, h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.1, smul_add]
    exact funext hd
  have e (s : OnePoint ℂ) : A.integral ((famAtlas A).pullback A (fib s) α) + A.integral ((famAtlas A).pullback A (fib s) β) =
      A.integral ((famAtlas A).pullback A (fib s) (α + β)) := by
    have Q := (P M 1 A _ (isHolo_fib A s)).2
    have ha := ((Q 0 α α).2.2.2 hα.1).1
    have hb := ((Q 0 β β).2.2.2 hβ.1).1
    have := HolAtlas.integral_sub_of_isForm A _ _ (C' 0 _ _ ha hb).1 hb
    rw [add_sub_cancel_right] at this
    rw [(Q 0 α β).1, this, sub_add_cancel]
  rw [e, e]
  exact integral_fib_eq_of_ddc_eq_zero A h1.1 hd' t t'

end GlobalTheory.BcUnique
