import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtEntry

open Set Filter Metric Topology
open scoped ContDiff

namespace GlobalTheory.InjHol

theorem exists_zero_of_norm_lt {φ : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (closedBall c r)) (h : ∀ t ∈ sphere c r, ‖φ c‖ < ‖φ t‖) :
    ∃ t ∈ closedBall c r, φ t = 0 := by
  by_contra hne
  push Not at hne
  have hd : DiffContOnCl ℂ (fun t => (φ t)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    exact hφ.inv hne
  obtain ⟨t, ht, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
    (nonempty_ball.mpr hr) hd
  rw [frontier_ball c hr.ne'] at ht
  have h1 : ‖(φ c)⁻¹‖ ≤ ‖(φ t)⁻¹‖ := hmax (subset_closure (mem_ball_self hr))
  rw [norm_inv, norm_inv] at h1
  have h2 : 0 < ‖φ c‖ := norm_pos_iff.mpr (hne c (mem_closedBall_self hr.le))
  exact absurd (inv_strictAnti₀ h2 (h t ht)) (not_lt.mpr h1)

theorem not_injOn_of_fderiv_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Nontrivial E] {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) (h0 : ∀ᶠ x in 𝓝 a, fderiv ℂ f x = 0) {s : Set E} (hs : s ∈ 𝓝 a) :
    ¬ InjOn f s := by
  intro hinj
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hf.eventually_analyticAt.and (h0.and hs))
  have hd : DifferentiableOn ℂ f (ball a r) := fun x hx =>
    (hb x hx).1.differentiableAt.differentiableWithinAt
  have hnb : (𝓝[≠] a).NeBot := Module.punctured_nhds_neBot ℂ E a
  obtain ⟨x, hx, hxa⟩ := ((show ∀ᶠ x in 𝓝[≠] a, x ∈ ball a r from
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr)).and self_mem_nhdsWithin).exists
  exact hxa (hinj (hb x hx).2.2 (mem_of_mem_nhds hs)
    (isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℂ) (convex_ball a r).isPreconnected hd
      (fun y hy => (hb y hy).2.1) hx (mem_ball_self hr)))

theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) {s : Set ℂ}
    (hs : s ∈ 𝓝 a) (hinj : InjOn f s) : deriv f a ≠ 0 := by
  intro h0
  obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.eventually_iff.mp (hf.eventually_analyticAt.and hs)
  have hd : DifferentiableOn ℂ f (closedBall a r) := fun x hx =>
    (hb hx).1.differentiableAt.differentiableWithinAt
  have hsym : ∀ w, dslope f w a = dslope f a w := by
    intro w
    by_cases hw : w = a
    · rw [hw]
    · rw [dslope_of_ne _ hw, dslope_of_ne _ (Ne.symm hw), slope_comm]
  have h1 : ∀ᶠ w in 𝓝 a, ∀ z ∈ sphere a r, ‖dslope f w a‖ < ‖dslope f w z‖ := by
    refine (isCompact_sphere a r).eventually_forall_of_forall_eventually fun z hz => ?_
    have hza : z ≠ a := ne_of_mem_sphere hz hr.ne'
    have hzc := (hb (sphere_subset_closedBall hz))
    have c1 : ContinuousAt (fun p : ℂ × ℂ => ‖dslope f a p.1‖) (a, z) :=
      (ContinuousAt.comp (f := Prod.fst) (x := (a, z))
        (continuousAt_dslope_same.mpr hf.differentiableAt) continuousAt_fst).norm
    have c2 : ContinuousAt (fun p : ℂ × ℂ => ‖(p.2 - p.1)⁻¹ * (f p.2 - f p.1)‖) (a, z) := by
      refine ContinuousAt.norm (ContinuousAt.mul (ContinuousAt.inv₀ (by fun_prop)
        (sub_ne_zero.mpr hza)) (ContinuousAt.sub ?_ ?_))
      · exact ContinuousAt.comp (f := Prod.snd) (x := (a, z)) hzc.1.continuousAt continuousAt_snd
      · exact ContinuousAt.comp (f := Prod.fst) (x := (a, z)) hf.continuousAt continuousAt_fst
    have hlt : ‖dslope f a a‖ < ‖(z - a)⁻¹ * (f z - f a)‖ := by
      rw [dslope_same, h0, norm_zero, norm_pos_iff]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hza))
        (sub_ne_zero.mpr fun h => hza (hinj hzc.2 (mem_of_mem_nhds hs) h))
    have hne : ∀ᶠ p : ℂ × ℂ in 𝓝 (a, z), p.2 ≠ p.1 :=
      (isOpen_ne_fun continuous_snd continuous_fst).mem_nhds hza
    filter_upwards [c1.eventually_lt c2 hlt, hne] with p hp hp'
    rw [hsym, dslope_of_ne _ hp', slope_def_module, smul_eq_mul]
    exact hp
  have h2 : ∀ᶠ w in 𝓝 a, fderiv ℂ f w = 0 := by
    filter_upwards [h1, ball_mem_nhds a hr] with w hw hwb
    obtain ⟨z, hz, hz0⟩ := exists_zero_of_norm_lt hr
      ((Complex.differentiableOn_dslope (mem_of_superset (isOpen_ball.mem_nhds hwb)
        ball_subset_closedBall)).mpr hd) hw
    by_cases hzw : z = w
    · rw [hzw, dslope_same] at hz0
      ext
      simpa using hz0
    · rw [dslope_of_ne _ hzw, slope_def_module, smul_eq_zero] at hz0
      rcases hz0 with h | h
      · exact absurd (sub_eq_zero.mp (inv_eq_zero.mp h)) hzw
      · exact absurd (hinj (hb hz).2 (hb (ball_subset_closedBall hwb)).2 (sub_eq_zero.mp h)) hzw
  exact not_injOn_of_fderiv_eq_zero hf h2 hs hinj

theorem exists_apply_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L : E →L[ℂ] ℂ} (h : L ≠ 0) : ∃ v, L v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (ContinuousLinearMap.ext hc)
  exact ⟨(L w)⁻¹ • w, by simp [hw]⟩

theorem exists_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : E → ℂ} {b : E} (hg : AnalyticAt ℂ g b) {L : E →L[ℂ] ℂ} (hL : HasFDerivAt g L b)
    (h0 : L ≠ 0) :
    ∃ ψ : L.ker → E, AnalyticAt ℂ ψ 0 ∧ ψ 0 = b ∧ HasFDerivAt ψ L.ker.subtypeL 0 ∧
      (∀ᶠ x in 𝓝 0, g (ψ x) = g b) ∧ ∃ s ∈ 𝓝 (0 : L.ker), InjOn ψ s := by
  obtain ⟨v, hv⟩ := exists_apply_eq_one h0
  let R : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ v
  have hR : Function.RightInverse R L := fun t => by simp [R, hv]
  let p := L.projKerOfRightInverse R hR
  let e : E ≃L[ℂ] ℂ × L.ker := ContinuousLinearEquiv.equivOfRightInverse L R hR
  let G : E → ℂ × L.ker := fun x => (g x, p (x - b))
  have hG : ContDiffAt ℂ ω G b :=
    (hg.prod ((p.analyticAt _).comp (analyticAt_id.sub analyticAt_const))).contDiffAt
  have hG' : HasFDerivAt G (e : E →L[ℂ] ℂ × L.ker) b := by
    have := hL.prodMk (p.hasFDerivAt.comp b ((hasFDerivAt_id b).sub_const b))
    exact this
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hGb : G b = (g b, 0) := by simp [G]
  let I := hG.localInverse hG' hω
  have hI : AnalyticAt ℂ I (g b, 0) := hGb ▸ (hG.to_localInverse hG' hω).analyticAt
  have hI0 : I (g b, 0) = b := hGb ▸ hG.localInverse_apply_image hG' hω
  have hI' : HasFDerivAt I (e.symm : ℂ × L.ker →L[ℂ] E) (g b, 0) :=
    hGb ▸ (hG.hasStrictFDerivAt' hG' hω).to_localInverse.hasFDerivAt
  have hri : ∀ᶠ y in 𝓝 (g b, (0 : L.ker)), G (I y) = y :=
    hGb ▸ (hG.hasStrictFDerivAt' hG' hω).eventually_right_inverse
  have hc : ContinuousAt (fun x : L.ker => (g b, x)) 0 := by fun_prop
  have hri' := hc.eventually hri
  refine ⟨fun x => I (g b, x), ?_, hI0, ?_, ?_, _, hri', ?_⟩
  · exact hI.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  · have := HasFDerivAt.comp (0 : L.ker) (f := fun x : L.ker => (g b, x)) hI'
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (g b) (0 : L.ker))
    convert! this
    ext x
    simp [e]
  · filter_upwards [hri'] with x hx
    exact congrArg Prod.fst hx
  · intro x hx y hy hxy
    have h1 : G (I (g b, x)) = (g b, x) := hx
    have h2 : G (I (g b, y)) = (g b, y) := hy
    have h3 : I (g b, x) = I (g b, y) := hxy
    rw [h3, h2] at h1
    exact (congrArg Prod.snd h1).symm

theorem eventually_zero_of_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {g h : E → ℂ} {b : E} (hg : AnalyticAt ℂ g b) (hh : AnalyticAt ℂ h b)
    (h0 : fderiv ℂ g b ≠ 0) (hb : h b = 0) (hsub : ∀ᶠ z in 𝓝 b, h z = 0 → g z = 0) :
    ∀ᶠ z in 𝓝 b, g z = 0 → h z = 0 := by
  obtain ⟨v, hv⟩ := exists_apply_eq_one h0
  have hgb : g b = 0 := hsub.self_of_nhds hb
  have hT : Tendsto (fun q : E × ℂ => q.1 + q.2 • v) (𝓝 (b, 0)) (𝓝 b) := by
    have : ContinuousAt (fun q : E × ℂ => q.1 + q.2 • v) (b, 0) := by fun_prop
    simpa using this.tendsto
  have hT1 : Tendsto (fun q : E × ℂ => q.1) (𝓝 (b, 0)) (𝓝 b) := continuous_fst.tendsto _
  have hc : 0 < (2 * (‖v‖ + 1))⁻¹ := by positivity
  have hst := (hg.hasStrictFDerivAt.isLittleO.def hc)
  rw [nhds_prod_eq] at hst
  have hQ : ∀ᶠ q : E × ℂ in 𝓝 (b, 0), AnalyticAt ℂ h (q.1 + q.2 • v) ∧
      (g q.1 = 0 → h (q.1 + q.2 • v) = 0 → q.2 = 0) := by
    filter_upwards [hT.eventually hh.eventually_analyticAt, hT.eventually hsub,
      (hT.prodMk hT1).eventually hst] with q h1 h2 h3
    refine ⟨h1, fun h4 h5 => ?_⟩
    simp only [h2 h5, h4, add_sub_cancel_left, map_smul, hv, smul_eq_mul, mul_one, sub_self,
      zero_sub, norm_neg, norm_smul] at h3
    have h6 : (2 * (‖v‖ + 1))⁻¹ * ‖v‖ ≤ 1 / 2 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith
    have h7 : ‖q.2‖ ≤ 0 := by nlinarith [norm_nonneg q.2]
    exact norm_le_zero_iff.mp h7
  have hc0 : ContinuousAt (fun t : ℂ => (b, t)) 0 := by fun_prop
  obtain ⟨r, hr, hball⟩ :=
    nhds_basis_closedBall.eventually_iff.mp (hc0.eventually hQ.eventually_nhds)
  have h1 := (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually
    (x₀ := b) (P := fun z t => AnalyticAt ℂ h (z + t • v) ∧ (g z = 0 → h (z + t • v) = 0 → t = 0))
    fun t ht => hball ht
  have h2 : ∀ᶠ z in 𝓝 b, ∀ t ∈ sphere (0 : ℂ) r, ‖h z‖ < ‖h (z + t • v)‖ := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => ?_
    have ht' := (hball (sphere_subset_closedBall ht)).self_of_nhds
    have c1 : ContinuousAt (fun q : E × ℂ => ‖h q.1‖) (b, t) :=
      (ContinuousAt.comp (f := Prod.fst) (x := (b, t)) hh.continuousAt continuousAt_fst).norm
    have c2 : ContinuousAt (fun q : E × ℂ => ‖h (q.1 + q.2 • v)‖) (b, t) :=
      (ContinuousAt.comp (f := fun q : E × ℂ => q.1 + q.2 • v) (x := (b, t))
        ht'.1.continuousAt (by fun_prop)).norm
    refine c1.eventually_lt c2 ?_
    simp only [hb, norm_zero, norm_pos_iff]
    exact fun h5 => ne_of_mem_sphere ht hr.ne' (ht'.2 hgb h5)
  filter_upwards [h1, h2] with z hz1 hz2 hgz
  obtain ⟨t, ht, ht0⟩ := exists_zero_of_norm_lt (φ := fun t => h (z + t • v)) hr
    (fun t ht => (DifferentiableAt.comp t (f := fun t : ℂ => z + t • v)
      (hz1 t ht).1.differentiableAt (by fun_prop)).differentiableWithinAt)
    (by simpa using hz2)
  have := (hz1 t ht).2 hgz ht0
  simpa [this] using ht0

theorem exists_regular_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {h : E → ℂ} {a : E} (hh : AnalyticAt ℂ h a) (ha : h a = 0) (hne : ¬ ∀ᶠ z in 𝓝 a, h z = 0)
    {W : Set E} (hW : W ∈ 𝓝 a) :
    ∃ b ∈ W, h b = 0 ∧ AnalyticAt ℂ h b ∧ ∃ g : E → ℂ, AnalyticAt ℂ g b ∧ fderiv ℂ g b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, h z = 0 → g z = 0 := by
  classical
  obtain ⟨U, hU, hUo, haU⟩ := _root_.eventually_nhds_iff.mp (hh.eventually_analyticAt.and hW)
  have hUa : AnalyticOnNhd ℂ h U := fun z hz => (hU z hz).1
  have hex : ∃ k, ∃ z ∈ U, h z = 0 ∧ iteratedFDeriv ℂ k h z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨p, r, hp⟩ := hh
    apply hne
    filter_upwards [eball_mem_nhds a hp.r_pos] with z hz
    have hz' : z - a ∈ Metric.eball (0 : E) r := by
      simpa [Metric.mem_eball, edist_eq_enorm_sub] using hz
    have := hp.hasSum_iteratedFDeriv hz'
    simp only [hc _ a haU ha, ContinuousMultilinearMap.zero_apply, smul_zero,
      add_sub_cancel] at this
    exact this.unique hasSum_zero
  obtain ⟨b, hbU, hb, hk⟩ := Nat.find_spec hex
  have hmin := fun j => Nat.find_min hex (m := j)
  generalize Nat.find hex = k at hk hmin
  cases k with
  | zero => exact absurd (by ext; simp [hb]) hk
  | succ j =>
    obtain ⟨m, hm⟩ : ∃ m, iteratedFDeriv ℂ (j + 1) h b m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hk (ContinuousMultilinearMap.ext hc)
    let A := ContinuousMultilinearMap.apply ℂ (fun _ : Fin j => E) ℂ (Fin.tail m)
    have hj := hUa.iteratedFDeriv j b hbU
    refine ⟨b, (hU b hbU).2, hb, hUa b hbU, fun z => A (iteratedFDeriv ℂ j h z),
      (A.analyticAt _).comp hj, fun h0 => hm ?_, ?_⟩
    · have := (A.hasFDerivAt.comp b hj.differentiableAt.hasFDerivAt).fderiv
      have h2 : A.comp (fderiv ℂ (iteratedFDeriv ℂ j h) b) = 0 := this.symm.trans h0
      rw [iteratedFDeriv_succ_apply_left]
      exact congrArg (fun T => T (m 0)) h2
    · filter_upwards [hUo.mem_nhds hbU] with z hz hz0
      have := hmin j (Nat.lt_succ_self j)
      push Not at this
      simp [this z hz hz0]

theorem analyticAt_det {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) :
    AnalyticAt ℂ (fun z => LinearMap.det (A z : E →ₗ[ℂ] E)) a := by
  first
  | exact @_root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det
  | exact _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det
  | (apply _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AnalyticMatrixEntries.analyticAt_det ..)

def LocalStatement (n : ℕ) : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F],
    Module.finrank ℂ E = n → Module.finrank ℂ F = n → ∀ (f : E → F) (a : E), AnalyticAt ℂ f a →
      (∃ s ∈ 𝓝 a, InjOn f s) → Function.Injective (fderiv ℂ f a)

theorem injective_of_fderiv_ne_zero {n : ℕ} (ih : LocalStatement n) {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hE : Module.finrank ℂ E = n + 1) (hF : Module.finrank ℂ F = n + 1) {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) {s : Set E} (hs : s ∈ 𝓝 a) (hinj : InjOn f s)
    (h0 : fderiv ℂ f a ≠ 0) : Function.Injective (fderiv ℂ f a) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℂ f a w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (ContinuousLinearMap.ext hc)
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
  let l : F →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  have hL0 : l.comp (fderiv ℂ f a) ≠ 0 := fun h => hl₀ (congrArg (fun T => T w) h)
  have hl0 : l ≠ 0 := fun h => hL0 (by simp [h])
  obtain ⟨ψ, hψ, hψ0, hψ', hψg, t, ht, hψi⟩ := exists_slice (g := fun x => l (f x))
    ((l.analyticAt _).comp hf) (l.hasFDerivAt.comp a hf.differentiableAt.hasFDerivAt) hL0
  obtain ⟨u, hu⟩ := exists_apply_eq_one hl0
  let R : ℂ →L[ℂ] F := ContinuousLinearMap.toSpanSingleton ℂ u
  have hR : Function.RightInverse R l := fun t => by simp [R, hu]
  let p := l.projKerOfRightInverse R hR
  have hK : Module.finrank ℂ (l.comp (fderiv ℂ f a)).ker = n := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := (l.comp (fderiv ℂ f a) : E →ₗ[ℂ] ℂ)) (fun h => hL0 (ContinuousLinearMap.coe_injective h))
    omega
  have hK' : Module.finrank ℂ l.ker = n := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := (l : F →ₗ[ℂ] ℂ)) (fun h => hl0 (ContinuousLinearMap.coe_injective h))
    omega
  have hs' : ∀ᶠ x in 𝓝 0, ψ x ∈ s := hψ.continuousAt.eventually (by rw [hψ0]; exact hs)
  have hfa : HasFDerivAt f (fderiv ℂ f a) (ψ 0) := by
    rw [hψ0]
    exact hf.differentiableAt.hasFDerivAt
  have key := ih _ _ hK hK' (fun x => p (f (ψ x))) 0
    ((p.analyticAt _).comp (hf.comp_of_eq hψ hψ0))
    ⟨_, inter_mem ht (hs'.and hψg), fun x hx y hy hxy => by
      refine hψi hx.1 hy.1 (hinj hx.2.1 hy.2.1 ?_)
      have h1 : f (ψ x) - R (l (f (ψ x))) = f (ψ y) - R (l (f (ψ y))) := congrArg Subtype.val hxy
      rw [hx.2.2, hy.2.2] at h1
      exact sub_left_injective h1⟩
  have hd := (p.hasFDerivAt.comp 0 (hfa.comp 0 hψ')).fderiv
  rw [show fderiv ℂ (fun x => p (f (ψ x))) 0 = _ from hd] at key
  rw [injective_iff_map_eq_zero] at key ⊢
  intro x hx
  exact congrArg Subtype.val (key ⟨x, by simp [hx]⟩ (by
    change p (fderiv ℂ f a x) = 0
    rw [hx, map_zero]))

theorem localStatement (n : ℕ) : LocalStatement n := by
  induction n with
  | zero =>
    intro E F _ _ _ _ _ _ hE _ f a _ _
    haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
    exact Function.injective_of_subsingleton _
  | succ n ih =>
    rintro E F _ _ _ _ _ _ hE hF f a hf ⟨s, hs, hinj⟩
    haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
    haveI : CompleteSpace F := FiniteDimensional.complete ℂ F
    haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    refine injective_of_fderiv_ne_zero ih hE hF hf hs hinj fun h0 => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨eE⟩ : Nonempty (ℂ ≃L[ℂ] E) :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hE])
      obtain ⟨eF⟩ : Nonempty (F ≃L[ℂ] ℂ) :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hF])
      obtain ⟨c, rfl⟩ := eE.surjective a
      refine deriv_ne_zero_of_injOn (f := fun t => eF (f (eE t))) (a := c)
        ((eF.analyticAt _).comp (hf.comp (eE.analyticAt _)))
        (eE.continuous.continuousAt.preimage_mem_nhds hs)
        (fun x hx y hy hxy => eE.injective (hinj hx hy (eF.injective hxy))) ?_
      have := (eF.hasFDerivAt.comp c
        (hf.differentiableAt.hasFDerivAt.comp c eE.hasFDerivAt)).hasDerivAt.deriv
      refine this.trans ?_
      simp [h0]
    · obtain ⟨e⟩ : Nonempty (F ≃L[ℂ] E) :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (hF.trans hE.symm)
      let A : E → E →L[ℂ] E := fun z => (e : F →L[ℂ] E).comp (fderiv ℂ f z)
      let h : E → ℂ := fun z => LinearMap.det (A z : E →ₗ[ℂ] E)
      have hh : AnalyticAt ℂ h a :=
        analyticAt_det (((ContinuousLinearMap.compL ℂ E F E (e : F →L[ℂ] E)).analyticAt _).comp
          hf.fderiv)
      have hW : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ f z ∧ s ∈ 𝓝 z :=
        hf.eventually_analyticAt.and (eventually_mem_nhds_iff.mpr hs)
      have hZ : ∀ z, AnalyticAt ℂ f z ∧ s ∈ 𝓝 z → h z = 0 → fderiv ℂ f z = 0 := by
        intro z hz hz0
        by_contra hne
        have hi := injective_of_fderiv_ne_zero ih hE hF hz.1 hz.2 hinj hne
        exact LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz0
          (LinearMap.ker_eq_bot.mpr (e.injective.comp hi))
      have ha : h a = 0 := by
        refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ?_
        simp [A, h0]
      have hne : ¬ ∀ᶠ z in 𝓝 a, h z = 0 := fun hc =>
        not_injOn_of_fderiv_eq_zero hf (by filter_upwards [hW, hc] using hZ) hs hinj
      obtain ⟨b, hb, hb0, hhb, g, hg, hg0, hsub⟩ := exists_regular_of_zero hh ha hne hW
      have hgb : g b = 0 := hsub.self_of_nhds hb0
      have hfill := eventually_zero_of_subset hg hhb hg0 hb0 hsub
      obtain ⟨ψ, hψ, hψ0, -, hψg, t, ht, hψi⟩ :=
        exists_slice hg hg.differentiableAt.hasFDerivAt hg0
      haveI : Nontrivial (fderiv ℂ g b).ker := by
        have := Module.Dual.finrank_ker_add_one_of_ne_zero
          (f := (fderiv ℂ g b : E →ₗ[ℂ] ℂ)) (fun h => hg0 (ContinuousLinearMap.coe_injective h))
        exact Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      have hT : Tendsto ψ (𝓝 0) (𝓝 b) := by
        have := hψ.continuousAt.tendsto
        rwa [hψ0] at this
      have hWb : ∀ᶠ z in 𝓝 b, AnalyticAt ℂ f z ∧ s ∈ 𝓝 z :=
        hb.1.eventually_analyticAt.and (eventually_mem_nhds_iff.mpr hb.2)
      refine not_injOn_of_fderiv_eq_zero (f := fun x => f (ψ x)) (hb.1.comp_of_eq hψ hψ0) ?_
        (inter_mem ht (hT hb.2)) fun x hx y hy hxy => hψi hx.1 hy.1 (hinj hx.2 hy.2 hxy)
      filter_upwards [hT.eventually hWb, hT.eventually hfill, hψg, hψ.eventually_analyticAt]
        with x h1 h2 h3 h4
      have := (h1.1.differentiableAt.hasFDerivAt.comp x h4.differentiableAt.hasFDerivAt).fderiv
      refine this.trans ?_
      simp [hZ _ h1 (h2 (h3.trans hgb))]

theorem bijective_fderiv_of_injOn :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen U →
      DifferentiableOn ℂ f U → Set.InjOn f U → ∀ a ∈ U, Function.Bijective (fderiv ℂ f a) := by
  intro n U f hU hf hinj a ha
  have han : AnalyticAt ℂ f a := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha
  have hi := localStatement n _ _ (by simp) (by simp) f a han ⟨U, hU.mem_nhds ha, hinj⟩
  exact ⟨hi, LinearMap.injective_iff_surjective.mp
    (show Function.Injective (fderiv ℂ f a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) from hi)⟩

end GlobalTheory.InjHol
