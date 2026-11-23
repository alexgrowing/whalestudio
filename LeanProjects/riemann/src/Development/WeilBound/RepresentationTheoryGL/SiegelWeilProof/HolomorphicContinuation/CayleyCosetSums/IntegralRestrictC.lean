import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Nonzero
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hLoc_nonneg' (g : GR n) : 0 ≤ hLoc g := by unfold hLoc; positivity

theorem hLoc_pos' (g : GR n) : 0 < hLoc g := Vac.hLoc_pos detU1 g

theorem hLoc_slit (g : GR n) : ((hLoc g : ℝ) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (hLoc_pos' g)

theorem continuous_phi (m : ℕ) (e : ℤ) (w : ℂ) : Continuous (phi (n := n) m e w) := by
  unfold phi
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  exact (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)).cpow continuous_const fun g => hLoc_slit g

theorem continuous_phi₂ (m : ℕ) (e : ℤ) :
    Continuous fun p : GR n × ℂ => phi m e p.2 p.1 := by
  unfold phi
  refine ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_fst).mul ?_
  exact (Complex.continuous_ofReal.comp ((Vac.continuous_hLoc detU1).comp continuous_fst)).cpow continuous_snd
    fun p => hLoc_slit p.1

theorem differentiable_phi (m : ℕ) (e : ℤ) (u : GR n) : Differentiable ℂ fun w => phi m e w u := by
  unfold phi
  have h0 : ((hLoc u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hLoc_pos' u).ne'
  exact (differentiable_const _).mul (differentiable_id.const_cpow (Or.inl h0))

section

variable {m : ℕ} {e : ℤ} (ν : Measure (GR n)) (μK : Measure (KR n)) {β : M2 n → ℝ}

theorem twC (hβs : HasCompactSupport β) : IsCompact ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) :=
  isCompact_preimage_mR (tw_support m e μK hβs)

theorem tw_zero_off {u : GR n} (hu : u ∉ (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) : tw m e μK β (mR u) = 0 :=
  image_eq_zero_of_notMem_tsupport hu

theorem continuous_twR [IsFiniteMeasure μK] (hβc : Continuous β) : Continuous fun u : GR n => tw m e μK β (mR u) := by
  have hF : Continuous fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀
      (fun k => Vac.spherical_section_ne_zero detU1 m 0 e _)
  have hc : Continuous (Function.uncurry fun (X : M2 n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ)) := by
    refine (hF.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hβc.comp ?_))
    exact ((continuous_mR.comp (continuous_subtype_val.comp continuous_snd)).matrix_conjTranspose).matrix_mul
      continuous_fst
  have h := continuous_parametric_integral_of_continuous (μ := μK) hc isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h.comp continuous_mR

theorem integral_restrict_C (F : GR n → ℂ) (hF : ∀ u, u ∉ (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β) → F u = 0) :
    ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem cw_differentiable [ν.IsHaarMeasure] [μK.IsHaarMeasure] (hβc : Continuous β) (hβs : HasCompactSupport β) :
    Differentiable ℂ fun w => cw m e ν μK β w := by
  have hC := twC (m := m) (e := e) μK hβs
  haveI : IsFiniteMeasure (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
    isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have key := holParam (GR n) (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)))
    ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) hC
    (by rw [Measure.restrict_apply' hC.isClosed.measurableSet]; simp) univ
    (fun u w => phi m e w u * tw m e μK β (mR u)) isOpen_univ
    (by
      refine Continuous.continuousOn ?_
      exact ((continuous_phi₂ m e).comp (continuous_fst.prodMk continuous_snd)).mul
        (hcont.comp continuous_fst))
    (fun u _ => ((differentiable_phi m e u).mul_const _).differentiableOn)
  have heq : (fun w => cw m e ν μK β w) =
      fun w => ∫ u, phi m e w u * tw m e μK β (mR u) ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) := by
    funext w
    exact integral_restrict_C ν μK _ (fun u hu => by rw [tw_zero_off μK hu, mul_zero])
  rw [heq]
  exact differentiableOn_univ.mp key.1

end

section Glob

variable {m : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ}
  {U : Set ℂ} {d : Polynomial ℂ} {Ê : ℂ → G → ℂ} {t : ℝ}

theorem lhs_diff (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β)
    (g : G) (y : GR n) : DifferentiableOn ℂ (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) U := by
  have hC := twC (m := m) (e := e) μK hβs
  haveI : IsFiniteMeasure (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
    isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have hmap : Continuous fun q : GR n × ℂ => (q.2, g * ι (y * q.1)) :=
    continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp (continuous_const.mul continuous_fst)))
  have key := holParam (GR n) (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)))
    ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) hC
    (by rw [Measure.restrict_apply' hC.isClosed.measurableSet]; simp) U
    (fun u z => Ê z (g * ι (y * u)) * tw m e μK β (mR u)) hD.hU
    (by
      refine ContinuousOn.mul ?_ (hcont.comp continuous_fst).continuousOn
      refine hD.cont.comp hmap.continuousOn ?_
      intro q hq
      exact ⟨hq.2, mem_univ _⟩)
    (fun u _ => (hD.hol (g * ι (y * u))).mul_const _)
  have heq : (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) =
      fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u)
        ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) := by
    funext z
    exact integral_restrict_C ν μK _ (fun u hu => by rw [tw_zero_off μK hu, mul_zero])
  rw [heq]
  exact key.1

theorem term_rep (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (w : ℂ) (g : G) (q : GlobalTheory.Eis.Cosets Pp Γ) :
    ∃ (c : ℂ) (y₀ : GR n), ∀ v : GR n,
      GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ w * f x) (g * ι v) q = c * phi m e w (y₀ * v) := by
  obtain ⟨x₀, y₀, S, r, hr, hxy, hp⟩ := hD.split (((q.out : Γ) : G) * g)
  refine ⟨(r : ℂ) ^ w * S, y₀, fun v => ?_⟩
  have e1 : ((q.out : Γ) : G) * (g * ι v) = x₀ * ι (y₀ * v) := by rw [← mul_assoc, hxy, map_mul, mul_assoc]
  show ((Ht (((q.out : Γ) : G) * (g * ι v)) : ℝ) : ℂ) ^ w * f (((q.out : Γ) : G) * (g * ι v)) = _
  rw [e1, (hp (y₀ * v)).1, (hp (y₀ * v)).2, phi, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg' _)]
  ring

theorem conv_far (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β)
    (z : ℂ) (hz : t < z.re) (g : G) (y : GR n) :
    ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
  obtain ⟨hfar, hE⟩ := hD.far z hz
  set Φ : G → ℂ := fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x with hΦ
  set C := (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β) with hCdef
  have hC : IsCompact C := twC μK hβs
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have hι : Continuous fun u : GR n => g * ι (y * u) :=
    continuous_const.mul (hD.ιc.comp (continuous_const.mul continuous_id))
  obtain ⟨b, hb, hbd⟩ := hfar (insert (g * ι y) ((fun u => g * ι (y * u)) '' C)) ((hC.image hι).insert _)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  haveI : Countable (Function.support b) := hb.countable_support.to_subtype
  have hmemC : ∀ u ∈ C, g * ι (y * u) ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C) :=
    fun u hu => mem_insert_of_mem _ ⟨u, hu, rfl⟩
  have hzero : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C), ∀ q,
      q ∉ Function.support b → GlobalTheory.Eis.term Pp Γ Φ h q = 0 := by
    intro h hh q hq
    have h1 := hbd h hh q
    rw [Function.notMem_support.mp hq] at h1
    exact norm_le_zero_iff.mp h1
  have hsum_eq : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C),
      GlobalTheory.Eis.cosetSum Pp Γ Φ h = ∑' q : Function.support b, GlobalTheory.Eis.term Pp Γ Φ h q := by
    intro h hh
    unfold GlobalTheory.Eis.cosetSum
    exact (tsum_subtype_eq_of_support_subset
      (fun q hq => by_contra fun hq' => hq (hzero h hh q hq'))).symm
  have hsumm : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C),
      Summable fun q : Function.support b => GlobalTheory.Eis.term Pp Γ Φ h q :=
    fun h hh => Summable.of_norm_bounded (hb.subtype _) (fun q => hbd h hh q)
  have hvan : ∀ F : GR n → ℂ, ∀ u, u ∉ C → F u * tw m e μK β (mR u) = 0 :=
    fun F u hu => by rw [tw_zero_off μK hu, mul_zero]
  have hrep : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, ∃ (c : ℂ) (y₀ : GR n), ∀ v : GR n,
      GlobalTheory.Eis.term Pp Γ Φ (g * ι v) q = c * phi m e (z - s₀) (y₀ * v) := by
    intro q
    obtain ⟨c, y₀, hc⟩ := term_rep hD (z - s₀) g q
    exact ⟨c, y₀, fun v => by rw [hΦ]; exact hc v⟩
  have hterm : ∀ q : GlobalTheory.Eis.Cosets Pp Γ,
      ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂ν =
        cw m e ν μK β (z - s₀) * GlobalTheory.Eis.term Pp Γ Φ (g * ι y) q := by
    intro q
    obtain ⟨c, y₀, hc⟩ := hrep q
    simp only [hc, mul_assoc c]
    rw [integral_const_mul]
    simp only [← mul_assoc y₀ y]
    rw [conv_phi]
    ring
  have hmeas : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, AEStronglyMeasurable
      (fun u => GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u)) (ν.restrict C) := by
    intro q
    obtain ⟨c, y₀, hc⟩ := hrep q
    have hcq : Continuous fun u : GR n =>
        c * phi m e (z - s₀) (y₀ * (y * u)) * tw m e μK β (mR u) :=
      (continuous_const.mul ((continuous_phi m e (z - s₀)).comp
        (continuous_const.mul (continuous_const.mul continuous_id)))).mul hcont
    simp only [hc]
    exact hcq.aestronglyMeasurable
  have hHas : HasSum
      (fun q : Function.support b =>
        ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂(ν.restrict C))
      (∫ u, (∑' q : Function.support b, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q) *
        tw m e μK β (mR u) ∂(ν.restrict C)) := by
    refine hasSum_integral_of_dominated_convergence (fun q _ => b q * M) (fun q => hmeas q) ?_ ?_ ?_ ?_
    · intro q
      filter_upwards [ae_restrict_mem hCm] with u hu
      rw [norm_mul]
      have h1 := hbd _ (hmemC u hu) q
      exact mul_le_mul h1 (hM u hu) (norm_nonneg _) ((norm_nonneg _).trans h1)
    · exact Eventually.of_forall fun _ => (hb.subtype _).mul_right M
    · exact integrable_const _
    · filter_upwards [ae_restrict_mem hCm] with u hu
      exact (hsumm _ (hmemC u hu)).hasSum.mul_right _
  calc ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν
      = ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂(ν.restrict C) :=
        integral_restrict_C ν μK _ (hvan _)
    _ = ∫ u, Polynomial.eval z d * ((∑' q : Function.support b,
          GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q) * tw m e μK β (mR u)) ∂(ν.restrict C) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hCm] with u hu
        rw [hE, hsum_eq _ (hmemC u hu)]
        ring
    _ = Polynomial.eval z d * ∑' q : Function.support b,
          ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂(ν.restrict C) := by
        rw [integral_const_mul, hHas.tsum_eq]
    _ = Polynomial.eval z d * ∑' q : Function.support b,
          cw m e ν μK β (z - s₀) * GlobalTheory.Eis.term Pp Γ Φ (g * ι y) q := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [← integral_restrict_C ν μK _ (hvan _), hterm]
    _ = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
        rw [tsum_mul_left, hE, hsum_eq _ (mem_insert _ _)]
        ring

theorem conv_U (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    ∀ z ∈ U, ∀ (g : G) (y : GR n),
      ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
  intro z hz g y
  obtain ⟨σ, hσ⟩ := hD.hR.1
  have hz0U : (((max σ t + 1 : ℝ)) : ℂ) ∈ U := by
    apply hσ
    simp only [GlobalTheory.Cont.rightOf, mem_setOf_eq, Complex.ofReal_re]
    linarith [le_max_left σ t]
  have hL : AnalyticOnNhd ℂ (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) U :=
    (lhs_diff hD ν μK hβc hβs g y).analyticOnNhd hD.hU
  have hdc : Differentiable ℂ fun z : ℂ => cw m e ν μK β (z - s₀) :=
    (cw_differentiable ν μK hβc hβs).comp (differentiable_id.sub_const s₀)
  have hR : AnalyticOnNhd ℂ (fun z => cw m e ν μK β (z - s₀) * Ê z (g * ι y)) U :=
    (hdc.differentiableOn.mul (hD.hol _)).analyticOnNhd hD.hU
  have hev : (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) =ᶠ[𝓝 (((max σ t + 1 : ℝ)) : ℂ)]
      (fun z => cw m e ν μK β (z - s₀) * Ê z (g * ι y)) := by
    have hopen : IsOpen {w : ℂ | t < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (((max σ t + 1 : ℝ)) : ℂ) ∈ {w : ℂ | t < w.re} := by
      simp only [mem_setOf_eq, Complex.ofReal_re]
      linarith [le_max_right σ t]
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact conv_far hD ν μK hβc hβs w hw g y
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hD.hR.isPreconnected hz0U hev hz

end Glob

end PositivityTheory.Rg.Sw.HSt.Conv
