import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.MultOne

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped ContDiff InnerProductSpace

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)

theorem hasDerivAt_orbit_smul {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) (t : ℝ) :
    HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v) (π (h.expG (t • X)) (h.derivOp π X v)) t := by
  have h0 := h.hasDerivAt_derivOp π hv X
  have h0' : HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v) (h.derivOp π X v) (t - t) := by
    rw [sub_self]; exact h0
  have h1 : HasDerivAt (fun s : ℝ => π (h.expG ((s - t) • X)) v) (h.derivOp π X v) t :=
    h0'.comp_sub_const t t
  have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [← BanachRep.map_mul_apply, ← h.expG_add_smul, add_sub_cancel]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem derivOp_integral (hπ : ∀ g, ‖π g‖ ≤ 1) {f : G → ℂ} (hf : h.IsTestFunction f)
    {u : G → E} (hu : Continuous u) (hus : ∀ g, h.IsSmoothVector π (u g)) (X : 𝔤)
    (hdu : Continuous fun g => h.derivOp π X (u g))
    (hz : h.IsSmoothVector π (∫ g, f g • u g ∂μ)) :
    h.derivOp π X (∫ g, f g • u g ∂μ) = ∫ g, f g • h.derivOp π X (u g) ∂μ := by
  have := secondCountableTopology_subgroup_units G
  have hfc := hf.continuous h
  have hint : Integrable (fun g => f g • u g) μ :=
    (hfc.smul hu).integrable_of_hasCompactSupport hf.2.smul_right
  set F : ℝ → G → E := fun t g => f g • π (h.expG (t • X)) (u g) with hF
  set F' : ℝ → G → E := fun t g => f g • π (h.expG (t • X)) (h.derivOp π X (u g)) with hF'
  have hcontF : ∀ t, Continuous (F t) := fun t =>
    hfc.smul ((π (h.expG (t • X))).continuous.comp hu)
  have hcontF' : ∀ t, Continuous (F' t) := fun t =>
    hfc.smul ((π (h.expG (t • X))).continuous.comp hdu)
  have hbound_int : Integrable (fun g => ‖f g‖ * ‖h.derivOp π X (u g)‖) μ :=
    ((continuous_norm.comp hfc).mul (continuous_norm.comp hdu)).integrable_of_hasCompactSupport
      (hf.2.norm.mul_right)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := 0)
    (bound := fun g => ‖f g‖ * ‖h.derivOp π X (u g)‖) (univ_mem)
    (Eventually.of_forall fun t => (hcontF t).aestronglyMeasurable)
    ((hcontF 0).integrable_of_hasCompactSupport (by
      simp only [hF]; exact hf.2.smul_right))
    (F' := F') (hcontF' 0).aestronglyMeasurable
    (Eventually.of_forall fun g t _ => by
      simp only [hF', norm_smul]
      gcongr
      calc ‖π (h.expG (t • X)) (h.derivOp π X (u g))‖
          ≤ ‖π (h.expG (t • X))‖ * ‖h.derivOp π X (u g)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖h.derivOp π X (u g)‖ := by gcongr; exact hπ _
        _ = _ := one_mul _) hbound_int
    (Eventually.of_forall fun g t _ => (h.hasDerivAt_orbit_smul π (hus g) X t).const_smul (f g))
  have e1 : (fun t : ℝ => ∫ g, F t g ∂μ) = fun t => π (h.expG (t • X)) (∫ g, f g • u g ∂μ) := by
    funext t
    rw [← (π (h.expG (t • X))).integral_comp_comm hint]
    simp [hF]
  have e2 : (∫ g, F' 0 g ∂μ) = ∫ g, f g • h.derivOp π X (u g) ∂μ := by
    simp [hF']
  rw [e1, e2] at key
  exact (h.hasDerivAt_derivOp π hz X).unique key.2

theorem wordOp_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) {w : E} (hw : h.IsSmoothVector π w)
    {f : G → ℂ} (hf : h.IsTestFunction f) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      h.wordOp π Y (π.integrated μ f w) = ∫ g, f g • h.wordOp π Y (π g w) ∂μ
  | 0, _ => rfl
  | k + 1, Y => by
    rw [wordOp_succ, wordOp_integrated hπ hw hf (Fin.tail Y)]
    have hus : ∀ g, h.IsSmoothVector π (h.wordOp π (Fin.tail Y) (π g w)) := fun g =>
      h.isSmoothVector_wordOp π (h.isSmoothVector_map π hw g) _
    have hz : h.IsSmoothVector π (∫ g, f g • h.wordOp π (Fin.tail Y) (π g w) ∂μ) := by
      rw [← wordOp_integrated hπ hw hf (Fin.tail Y)]
      exact h.isSmoothVector_wordOp π (h.isSmoothVector_integrated π μ hf w) _
    rw [h.derivOp_integral π μ hπ hf (h.continuous_wordOp_map π hπ hw _) hus (Y 0)
      (by simpa [wordOp_succ] using h.continuous_wordOp_map π hπ hw Y) hz]
    rfl

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped ContDiff InnerProductSpace

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)

noncomputable def testDeriv (X : 𝔤) (f : G → ℂ) (g : G) : ℂ :=
  deriv (fun t : ℝ => f (h.expG (-(t • X)) * g)) 0

theorem contDiff_testDeriv_exp {f : G → ℂ} (hf : h.IsTestFunction f) (X : 𝔤) (g₀ : G) :
    ContDiff ℝ ∞ (fun q : ℝ × 𝔤 => f (h.expG (-(q.1 • X)) * (g₀ * h.expG q.2))) := by
  have := h.contDiff_comp_expG_mul_expG hf.1 (φ₁ := fun q : ℝ × 𝔤 => -(q.1 • X)) (contDiff_fst.smul contDiff_const).neg g₀
    (φ₂ := fun q : ℝ × 𝔤 => q.2) contDiff_snd
  simpa [mul_assoc] using this

theorem isTestFunction_testDeriv {f : G → ℂ} (hf : h.IsTestFunction f) (X : 𝔤) :
    h.IsTestFunction (h.testDeriv X f) := by
  refine ⟨?_, ?_⟩
  · rw [h.contMDiff_iff_expG]
    intro g₀
    have hΨ : ContDiff ℝ ∞ (fun p : 𝔤 × ℝ => f (h.expG (-(p.2 • X)) * (g₀ * h.expG p.1))) := by
      have := h.contDiff_testDeriv_exp hf X g₀
      exact this.comp (contDiff_snd.prodMk contDiff_fst)
    have hd : ContDiff ℝ ∞ (fun Z : 𝔤 =>
        fderiv ℝ (fun t : ℝ => f (h.expG (-(t • X)) * (g₀ * h.expG Z))) 0) :=
      ContDiff.fderiv (f := fun Z t => f (h.expG (-(t • X)) * (g₀ * h.expG Z))) hΨ contDiff_const
        (by simp)
    exact hd.clm_apply contDiff_const
  · refine HasCompactSupport.mono' hf.2 fun g hg => ?_
    by_contra hgs
    apply hg
    have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
    have hc : Continuous fun t : ℝ => h.expG (-(t • X)) * g :=
      (h.continuous_expG.comp (continuous_id.smul continuous_const).neg).mul continuous_const
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), f (h.expG (-(t • X)) * g) = 0 := by
      have : (fun t : ℝ => h.expG (-(t • X)) * g) ⁻¹' (tsupport f)ᶜ ∈ 𝓝 (0 : ℝ) :=
        hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simpa using hgs))
      filter_upwards [this] with t ht
      exact image_eq_zero_of_notMem_tsupport ht
    show deriv _ 0 = 0
    rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) hev]
    simp

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem map_expG_integrated {f : G → ℂ} (hf : h.IsTestFunction f) (x : E) (Y : 𝔤) :
    π (h.expG Y) (π.integrated μ f x) = ∫ g, f (h.expG (-Y) * g) • π g x ∂μ := by
  have := secondCountableTopology_subgroup_units G
  rw [BanachRep.integrated, ← (π (h.expG Y)).integral_comp_comm (h.integrable_smul_orbit π μ hf x)]
  rw [← integral_mul_left_eq_self (fun g => f (h.expG (-Y) * g) • π g x) (h.expG Y)]
  congr 1
  funext g
  simp only [map_smul, ← BanachRep.map_mul_apply, expG_neg, inv_mul_cancel_left]

theorem derivOp_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) {f : G → ℂ} (hf : h.IsTestFunction f)
    (x : E) (X : 𝔤) :
    h.derivOp π X (π.integrated μ f x) = π.integrated μ (h.testDeriv X f) x := by
  have := secondCountableTopology_subgroup_units G
  have hz := h.isSmoothVector_integrated π μ hf x
  set ψ : ℝ → G → ℂ := fun s g => f (h.expG (-(s • X)) * g) with hψ
  set D : ℝ → G → ℂ := fun t g => deriv (fun s => ψ s g) t with hD
  have hψs : ∀ g, ContDiff ℝ ∞ (fun s => ψ s g) := fun g => by
    have e : (fun s => ψ s g) = (fun q : ℝ × 𝔤 => f (h.expG (-(q.1 • X)) * (g * h.expG q.2))) ∘
        (fun s : ℝ => (s, (0 : 𝔤))) := by
      funext s; simp [hψ]
    rw [e]
    exact (h.contDiff_testDeriv_exp hf X g).comp (contDiff_id.prodMk contDiff_const)
  have hDcont : Continuous (fun p : ℝ × G => D p.1 p.2) := by
    have hc := h.continuous_iteratedFDeriv_param ψ (fun g₀ => by
      simpa [hψ] using h.contDiff_testDeriv_exp hf X g₀) 1
    have e : (fun p : ℝ × G => D p.1 p.2) =
        fun p => iteratedFDeriv ℝ 1 (fun s => ψ s p.2) p.1 (fun _ => 1) := by
      funext p
      rw [iteratedFDeriv_one_apply]
      rfl
    rw [e]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ) ℂ (fun _ => (1 : ℝ))).continuous.comp hc

  set K' : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) '' (Icc (-1) 1 ×ˢ tsupport f) with hK'
  have hK'c : IsCompact K' :=
    (isCompact_Icc.prod hf.2).image ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul
      continuous_snd)
  have hDzero : ∀ t ∈ ball (0 : ℝ) 1, ∀ g ∉ K', D t g = 0 := by
    intro t ht g hg
    have hopen : IsOpen (ball (0 : ℝ) 1) := isOpen_ball
    have hev : ∀ᶠ s in 𝓝 t, ψ s g = 0 := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      show f (h.expG (-(s • X)) * g) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      apply hg
      refine ⟨(s, h.expG (-(s • X)) * g), ⟨?_, hmem⟩, ?_⟩
      · rw [mem_ball, Real.dist_eq, sub_zero] at hs
        exact ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
      · simp [expG_neg]
    show deriv _ t = 0
    rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) hev]
    simp
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK'c).exists_bound_of_continuousOn
    (f := fun p : ℝ × G => D p.1 p.2) hDcont.continuousOn
  set F : ℝ → G → E := fun t g => ψ t g • π g x with hF
  set F' : ℝ → G → E := fun t g => D t g • π g x with hF'
  have hcontF : ∀ t, Continuous (F t) := fun t =>
    (hf.continuous h |>.comp ((h.continuous_expG.comp continuous_const).mul continuous_id)).smul
      (π.continuous_orbit x)
  have hbound : Integrable (K'.indicator fun _ => M * ‖x‖) μ :=
    (integrable_indicator_iff hK'c.measurableSet).2 (integrableOn_const hK'c.measure_lt_top.ne)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := 0)
    (bound := K'.indicator fun _ => M * ‖x‖) (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t => (hcontF t).aestronglyMeasurable)
    ((hcontF 0).integrable_of_hasCompactSupport (by
      simp only [hF, hψ, zero_smul, neg_zero, expG_zero, one_mul]
      exact hf.2.smul_right))
    (F' := F') ((hDcont.comp (continuous_const.prodMk continuous_id)).smul
      (π.continuous_orbit x)).aestronglyMeasurable
    (Eventually.of_forall fun g t ht => by
      simp only [hF', norm_smul]
      by_cases hg : g ∈ K'
      · rw [indicator_of_mem hg]
        have h1 : ‖D t g‖ ≤ M := hM (t, g) ⟨⟨by
          rw [mem_ball, Real.dist_eq, sub_zero] at ht
          linarith [neg_abs_le t], by
          rw [mem_ball, Real.dist_eq, sub_zero] at ht
          linarith [le_abs_self t]⟩, hg⟩
        have h2 : ‖π g x‖ ≤ ‖x‖ := by
          calc ‖π g x‖ ≤ ‖π g‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖x‖ := by gcongr; exact hπ _
            _ = ‖x‖ := one_mul _
        exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      · rw [indicator_of_notMem hg, hDzero t ht g hg, norm_zero, zero_mul])
    hbound
    (Eventually.of_forall fun g t _ =>
      ((hψs g).differentiable (by simp) t).hasDerivAt.smul_const (π g x))
  have e1 : (fun t : ℝ => ∫ g, F t g ∂μ) = fun t => π (h.expG (t • X)) (π.integrated μ f x) := by
    funext t
    rw [h.map_expG_integrated π μ hf x]
  rw [e1] at key
  exact (h.hasDerivAt_derivOp π hz X).unique key.2

theorem exists_wordOp_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) {f : G → ℂ} (hf : h.IsTestFunction f) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), ∃ f' : G → ℂ, h.IsTestFunction f' ∧
      ∀ x : E, h.wordOp π Y (π.integrated μ f x) = π.integrated μ f' x
  | 0, _ => ⟨f, hf, fun _ => rfl⟩
  | k + 1, Y => by
    obtain ⟨f', hf', e⟩ := exists_wordOp_integrated hπ hf (Fin.tail Y)
    refine ⟨h.testDeriv (Y 0) f', h.isTestFunction_testDeriv hf' (Y 0), fun x => ?_⟩
    rw [wordOp_succ, e, h.derivOp_integrated π μ hπ hf' x (Y 0)]

theorem norm_integrated_le (hπ : ∀ g, ‖π g‖ ≤ 1) {f : G → ℂ} (hf : h.IsTestFunction f) (x : E) :
    ‖π.integrated μ f x‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖x‖ := by
  have := secondCountableTopology_subgroup_units G
  rw [BanachRep.integrated]
  calc ‖∫ g, f g • π g x ∂μ‖ ≤ ∫ g, ‖f g • π g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ‖f g‖ * ‖x‖ ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (((hf.continuous h).norm.mul continuous_const).integrable_of_hasCompactSupport
            hf.2.norm.mul_right) (Eventually.of_forall fun g => ?_)
        show ‖f g • π g x‖ ≤ ‖f g‖ * ‖x‖
        rw [norm_smul]
        gcongr
        calc ‖π g x‖ ≤ ‖π g‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖x‖ := by gcongr; exact hπ _
          _ = ‖x‖ := one_mul _
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ := integral_mul_const _ _

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped ContDiff InnerProductSpace Manifold

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)

theorem integrated_add [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] {f : G → ℂ} (hf : h.IsTestFunction f) (x y : E) :
    π.integrated μ f (x + y) = π.integrated μ f x + π.integrated μ f y := by
  have := secondCountableTopology_subgroup_units G
  have hi : ∀ z : E, Integrable (fun g => f g • π g z) μ := fun z =>
    ((hf.continuous h).smul (π.continuous_orbit z)).integrable_of_hasCompactSupport hf.2.smul_right
  simp only [BanachRep.integrated, map_add, smul_add]
  exact integral_add (hi x) (hi y)

theorem integrated_smul [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    (f : G → ℂ) (c : ℂ) (x : E) :
    π.integrated μ f (c • x) = c • π.integrated μ f x := by
  simp only [BanachRep.integrated, map_smul, smul_comm _ c]
  exact integral_smul c _

theorem integral_pi_apply [MeasurableSpace G] {ι : Type*} [Fintype ι] {μ : Measure G} {F : G → ι → E}
    (hF : Integrable F μ) (i : ι) : (∫ g, F g ∂μ) i = ∫ g, F g i ∂μ := by
  have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).integral_comp_comm hF
  simpa using this.symm

theorem eq_zero_of_forall_map_eq_zero (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v)
    (hdense : (Submodule.span ℂ (range fun g => π g v)).topologicalClosure = ⊤)
    (hvan : ∀ g, l (h.smoothMap π hv g) = 0) : l = 0 := by
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have := h.locallyCompactSpace
  have := secondCountableTopology_subgroup_units G
  set μ : Measure G := Measure.haar
  obtain ⟨s, C, hC⟩ := hl

  let J : h.smoothVectors π →ₗ[ℂ] (s → E) :=
    { toFun := fun w Y => h.wordOp π Y.1.2 (w : E)
      map_add' := fun w w' => by
        funext Y; simp only [Submodule.coe_add, Pi.add_apply]; exact h.wordOp_add π w.2 w'.2 _
      map_smul' := fun c w => by
        funext Y; simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact h.wordOp_smul π w.2 c _ }
  have hJ : ∀ w, J w = fun Y => h.wordOp π Y.1.2 (w : E) := fun _ => rfl
  have hbd : ∀ w, ‖l w‖ ≤ |C| * s.card * ‖J w‖ := by
    intro w
    refine (hC w).trans ?_
    calc C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (w : E)‖ ≤ |C| * ∑ Y ∈ s, ‖h.wordOp π Y.2 (w : E)‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ ≤ |C| * ∑ _Y ∈ s, ‖J w‖ := by
          gcongr with Y hY
          exact norm_le_pi_norm (J w) ⟨Y, hY⟩
      _ = |C| * s.card * ‖J w‖ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hker : LinearMap.ker J ≤ LinearMap.ker l := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := hbd w
    rw [hw, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let Λ₀ : LinearMap.range J →ₗ[ℂ] ℂ :=
    ((LinearMap.ker J).liftQ l hker).comp (J.quotKerEquivRange.symm : LinearMap.range J ≃ₗ[ℂ] _).toLinearMap
  have hΛ₀ : ∀ w, Λ₀ ⟨J w, LinearMap.mem_range_self J w⟩ = l w := by
    intro w
    have : (J.quotKerEquivRange.symm ⟨J w, LinearMap.mem_range_self J w⟩) =
        Submodule.Quotient.mk w := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [Λ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
      Submodule.liftQ_apply]
  let Λ₀c : LinearMap.range J →L[ℂ] ℂ := Λ₀.mkContinuous (|C| * s.card) (by
    rintro ⟨z, w, rfl⟩
    rw [hΛ₀]
    exact hbd w)
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range J) Λ₀c
  have hlΛ : ∀ w, l w = Λ (J w) := fun w => by
    rw [← hΛ₀ w]
    exact (hΛ ⟨J w, LinearMap.mem_range_self J w⟩).symm

  have hint_orbit : ∀ (f : G → ℂ) (hf : h.IsTestFunction f) (w : E) (hw : h.IsSmoothVector π w),
      l ⟨π.integrated μ f w, h.isSmoothVector_integrated π μ hf w⟩ =
        ∫ g, f g * l (h.smoothMap π hw g) ∂μ := by
    intro f hf w hw
    have hJc : Continuous fun g => J (h.smoothMap π hw g) :=
      continuous_pi fun Y => h.continuous_wordOp_map π hπ hw Y.1.2
    have hFint : Integrable (fun g => f g • J (h.smoothMap π hw g)) μ :=
      ((hf.continuous h).smul hJc).integrable_of_hasCompactSupport hf.2.smul_right
    have hJint : J ⟨π.integrated μ f w, h.isSmoothVector_integrated π μ hf w⟩ =
        ∫ g, f g • J (h.smoothMap π hw g) ∂μ := by
      funext Y
      rw [integral_pi_apply hFint Y, hJ]
      exact h.wordOp_integrated π μ hπ hw hf Y.1.2
    rw [hlΛ, hJint, ← Λ.integral_comp_comm hFint]
    congr 1; funext g
    rw [map_smul, smul_eq_mul, ← hlΛ]

  have hvanish : ∀ (f : G → ℂ) (hf : h.IsTestFunction f) (x : E),
      l ⟨π.integrated μ f x, h.isSmoothVector_integrated π μ hf x⟩ = 0 := by
    intro f hf
    choose fY hfY hfYeq using fun Y : s => h.exists_wordOp_integrated π μ hπ hf Y.1.2
    set B : ℝ := ∑ Y : s, ∫ g, ‖fY Y g‖ ∂μ with hB
    let T : E →ₗ[ℂ] (s → E) :=
      { toFun := fun x Y => π.integrated μ (fY Y) x
        map_add' := fun x y => by funext Y; exact h.integrated_add π (hfY Y) x y
        map_smul' := fun c x => by funext Y; exact integrated_smul π (fY Y) c x }
    have hTb : ∀ x, ‖T x‖ ≤ B * ‖x‖ := by
      intro x
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun Y => ?_
      refine (h.norm_integrated_le π μ hπ (hfY Y) x).trans ?_
      gcongr
      exact Finset.single_le_sum (f := fun Y : s => ∫ g, ‖fY Y g‖ ∂μ)
        (fun Y _ => integral_nonneg fun g => norm_nonneg _) (Finset.mem_univ Y)
    let L : E →L[ℂ] ℂ := Λ.comp (T.mkContinuous B hTb)
    have hL : ∀ x, L x = l ⟨π.integrated μ f x, h.isSmoothVector_integrated π μ hf x⟩ := by
      intro x
      rw [hlΛ]
      show Λ (T x) = _
      congr 1
      funext Y
      exact (hfYeq Y x).symm
    have horb : ∀ g, L (π g v) = 0 := by
      intro g
      have hw : h.IsSmoothVector π (π g v) := h.isSmoothVector_map π hv g
      rw [hL, hint_orbit f hf (π g v) hw]
      have : ∀ g', l (h.smoothMap π hw g') = 0 := by
        intro g'
        have e : h.smoothMap π hw g' = h.smoothMap π hv (g' * g) := by
          apply Subtype.ext; simp
        rw [e, hvan]
      simp [this]
    have hker : Submodule.span ℂ (range fun g => π g v) ≤ LinearMap.ker (L : E →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact horb g
    have hcl := Submodule.topologicalClosure_minimal _ hker L.isClosed_ker
    rw [hdense] at hcl
    intro x
    rw [← hL]
    exact hcl Submodule.mem_top

  ext ⟨w, hw⟩
  simp only [LinearMap.zero_apply]
  have hbound : ∀ ε > 0, ‖l ⟨w, hw⟩‖ ≤ |C| * s.card * ε := by
    intro ε hε
    have hev : ∀ᶠ g in 𝓝 (1 : G), ∀ Y ∈ s, ‖h.wordOp π Y.2 (π g w) - h.wordOp π Y.2 w‖ < ε := by
      rw [Finset.eventually_all]
      intro Y _
      have hc := (h.continuous_wordOp_map π hπ hw Y.2).continuousAt (x := (1 : G))
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at hc
      simp only [BanachRep.map_one_apply] at hc
      exact hc.eventually (gt_mem_nhds hε)
    let _ := h.chartedSpace
    have := h.isManifold ∞
    obtain ⟨b, -, hbU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, 𝔤)) (1 : G)).mem_iff.1 hev
    set c : ℝ := ∫ g, b g ∂μ with hcdef
    have hc : 0 < c := b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      b.hasCompactSupport (fun x => b.nonneg) (x := 1) (by rw [b.eq_one]; exact one_ne_zero)
    set f : G → ℂ := fun g => ((c⁻¹ * b g : ℝ) : ℂ) with hfdef
    have hsupp : Function.support f ⊆ Function.support b := by
      intro g hg hb; apply hg; simp [hfdef, hb]
    have hf : h.IsTestFunction f := by
      refine ⟨?_, b.hasCompactSupport.mono hsupp⟩
      set L' : ℝ →L[ℝ] ℂ := c⁻¹ • Complex.ofRealCLM
      have e : f = L' ∘ b := by funext g; simp [L', hfdef]
      rw [e]
      exact L'.contDiff.comp_contMDiff b.contMDiff
    have hfint : Integrable f μ := (hf.continuous h).integrable_of_hasCompactSupport hf.2
    have hint1 : ∫ g, f g ∂μ = 1 := by
      show ∫ g, ((c⁻¹ * b g : ℝ) : ℂ) ∂μ = 1
      rw [integral_complex_ofReal, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne',
        Complex.ofReal_one]
    have hnormf : ∀ g, ‖f g‖ = c⁻¹ * b g := fun g => by
      rw [hfdef, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hc.le) b.nonneg)]
    have hz := h.isSmoothVector_integrated π μ hf w
    have h0 := hvanish f hf w
    have hdiff : l ⟨w, hw⟩ = l ⟨w - π.integrated μ f w, (h.smoothVectors π).sub_mem hw hz⟩ := by
      have : (⟨w - π.integrated μ f w, (h.smoothVectors π).sub_mem hw hz⟩ : h.smoothVectors π) =
          ⟨w, hw⟩ - ⟨π.integrated μ f w, hz⟩ := rfl
      rw [this, map_sub, h0, sub_zero]
    rw [hdiff]
    refine (hC _).trans ?_
    calc C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (w - π.integrated μ f w)‖
        ≤ |C| * ∑ Y ∈ s, ‖h.wordOp π Y.2 (w - π.integrated μ f w)‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ ≤ |C| * ∑ _Y ∈ s, ε := by
          gcongr with Y hY
          rw [h.wordOp_sub π hw hz, h.wordOp_integrated π μ hπ hw hf]
          have hiY : Integrable (fun g => f g • h.wordOp π Y.2 (π g w)) μ :=
            ((hf.continuous h).smul (h.continuous_wordOp_map π hπ hw Y.2)).integrable_of_hasCompactSupport
              hf.2.smul_right
          have e : h.wordOp π Y.2 w - ∫ g, f g • h.wordOp π Y.2 (π g w) ∂μ =
              ∫ g, f g • (h.wordOp π Y.2 w - h.wordOp π Y.2 (π g w)) ∂μ := by
            simp_rw [smul_sub]
            rw [integral_sub (hfint.smul_const _) hiY, integral_smul_const, hint1, one_smul]
          rw [e]
          have hb : ∀ g, ‖f g • (h.wordOp π Y.2 w - h.wordOp π Y.2 (π g w))‖ ≤ (c⁻¹ * b g) * ε := by
            intro g
            rw [norm_smul, hnormf]
            by_cases hbg : b g = 0
            · simp [hbg]
            · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.2 hc.le) b.nonneg)
              have := hbU (subset_tsupport _ hbg) Y hY
              rw [norm_sub_rev]
              exact this.le
          calc ‖∫ g, f g • (h.wordOp π Y.2 w - h.wordOp π Y.2 (π g w)) ∂μ‖
              ≤ ∫ g, (c⁻¹ * b g) * ε ∂μ :=
                norm_integral_le_of_norm_le ((b.continuous.integrable_of_hasCompactSupport
                  b.hasCompactSupport).const_mul c⁻¹ |>.mul_const _) (Eventually.of_forall hb)
            _ = ε := by
                rw [integral_mul_const, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne', one_mul]
      _ = |C| * s.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  by_contra hne
  have hpos : 0 < ‖l ⟨w, hw⟩‖ := norm_pos_iff.2 hne
  set K := |C| * s.card with hK
  have hK0 : 0 ≤ K := by positivity
  have := hbound (‖l ⟨w, hw⟩‖ / (2 * (K + 1))) (by positivity)
  have h2 : K * (‖l ⟨w, hw⟩‖ / (2 * (K + 1))) < ‖l ⟨w, hw⟩‖ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end IsExpLieAlgebra

end GroundTheory.Automorphic
