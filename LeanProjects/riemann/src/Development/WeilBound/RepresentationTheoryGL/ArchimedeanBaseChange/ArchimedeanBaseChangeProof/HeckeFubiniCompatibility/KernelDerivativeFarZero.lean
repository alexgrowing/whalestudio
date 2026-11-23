import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableG
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.BcB.CG

namespace GelP

section Gen

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]

def D1 (K : H → H → A) (x y : H) : H →L[ℝ] A :=
  (fderiv ℝ (Function.uncurry K) (x, y)).comp (ContinuousLinearMap.inl ℝ H H)

structure Good (U : Set H) (l : H → ℝ) (K : H → H → A) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ U)
  supp : ∃ R, ∀ x ∈ U, ∀ y ∈ U, R + l x < l y → K x y = 0

variable {U : Set H} (hU : IsOpen U) {l : H → ℝ} (hl : ContinuousOn l U)

include hU hl in
theorem isOpen_far (R : ℝ) : IsOpen (U ×ˢ U ∩ (fun p : H × H => (R + l p.1, l p.2)) ⁻¹' {q : ℝ × ℝ | q.1 < q.2}) := by
  have ho : IsOpen (U ×ˢ U) := hU.prod hU
  have h1 : ContinuousOn (fun p : H × H => R + l p.1) (U ×ˢ U) :=
    continuousOn_const.add (hl.comp continuousOn_fst fun p hp => hp.1)
  have h2 : ContinuousOn (fun p : H × H => l p.2) (U ×ˢ U) := hl.comp continuousOn_snd fun p hp => hp.2
  exact (h1.prodMk h2).isOpen_inter_preimage ho isOpen_lt_prod

include hU hl in
theorem kernel_derivative_far_zero {K : H → H → A} {R : ℝ} (hR : ∀ x ∈ U, ∀ y ∈ U, R + l x < l y → K x y = 0) {x y : H} (hx : x ∈ U)
    (hy : y ∈ U) (hl' : R + l x < l y) : D1 K x y = 0 := by
  have hev : Function.uncurry K =ᶠ[𝓝 (x, y)] fun _ => 0 :=
    Filter.eventually_of_mem ((isOpen_far hU hl R).mem_nhds ⟨⟨hx, hy⟩, hl'⟩) fun p hp => hR p.1 hp.1.1 p.2 hp.1.2 hp.2
  rw [D1, hev.fderiv_eq]
  simp

include hU hl in
theorem Good.d1 {K : H → H → A} (h : Good U l K) : Good U l (D1 K) := by
  refine ⟨?_, ?_⟩
  · have hD : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry K)) (U ×ˢ U) :=
      h.smooth.fderiv_of_isOpen (hU.prod hU) (by simp)
    exact hD.clm_comp contDiffOn_const
  · obtain ⟨R, hR⟩ := h.supp
    exact ⟨R, fun x hx y hy hl' => kernel_derivative_far_zero hU hl hR hx hy hl'⟩

variable [ProperSpace H] {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ]
  [BorelSpace Γ] (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {v : Γ → H} (hv : Continuous v) (hvU : ∀ y, v y ∈ U)
  (hlc : ∀ R, IsCompact {y | l (v y) ≤ R})
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] {φ : Γ → B} (hφ : Continuous φ)

include hU hl hv hvU hlc hφ in
theorem hasFDerivAt_Iop {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (L : A →L[ℝ] B →L[ℝ] W) {K : H → H → A} (hK : Good U l K) {x₀ : H} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ y, L (K x (v y)) (φ y) ∂μ) (∫ y, L.precompL H (D1 K x₀ (v y)) (φ y) ∂μ) x₀ := by
  obtain ⟨R, hR⟩ := hK.supp
  have ho : IsOpen (U ×ˢ U) := hU.prod hU
  have hD1 := hK.d1 hU hl
  obtain ⟨ε, hε, hB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx₀)
  have hBc : IsCompact (Metric.closedBall x₀ ε) := isCompact_closedBall x₀ ε
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Metric.closedBall x₀ ε, l x ≤ M := by
    obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn (hl.mono hB)
    exact ⟨M, fun x hx => (le_abs_self _).trans (hM x hx)⟩
  have hS : IsCompact {y | l (v y) ≤ R + M} := hlc _
  let F' : H → Γ → H →L[ℝ] W := fun x y => L.precompL H (D1 K x (v y)) (φ y)
  have hF'c : ContinuousOn (fun p : H × Γ => F' p.1 p.2) (Metric.closedBall x₀ ε ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : H × Γ => D1 K p.1 (v p.2)) (Metric.closedBall x₀ ε ×ˢ Set.univ) :=
      hD1.smooth.continuousOn.comp (f := fun p : H × Γ => (p.1, v p.2))
        (continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn fun p hp => ⟨hB hp.1, hvU _⟩
    exact ((L.precompL H).continuous.comp_continuousOn h1).clm_apply (hφ.comp continuous_snd).continuousOn
  obtain ⟨C, hC⟩ := (hBc.prod hS).exists_bound_of_continuousOn
    (hF'c.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
  have hF0 : ∀ x ∈ U, ∀ y, R + l x < l (v y) → F' x y = 0 := fun x hx y h => by
    simp only [F', kernel_derivative_far_zero hU hl hR hx (hvU y) h, map_zero, ContinuousLinearMap.zero_apply]
  have hb : ∀ y, ∀ x ∈ Metric.closedBall x₀ ε, ‖F' x y‖ ≤ {y | l (v y) ≤ R + M}.indicator (fun _ => C) y := by
    intro y x hx
    by_cases hy : y ∈ {y | l (v y) ≤ R + M}
    · simpa [Set.indicator_of_mem hy] using hC (x, y) ⟨hx, hy⟩
    · have hlt : R + l x < l (v y) := by
        have := hM x hx
        have h2 : R + M < l (v y) := not_le.1 hy
        linarith
      rw [Set.indicator_of_notMem hy, hF0 x (hB hx) y hlt, norm_zero]
  have hbi : Integrable ({y | l (v y) ≤ R + M}.indicator fun _ => C) μ :=
    (integrable_indicator_iff hS.measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  have hxB : x₀ ∈ Metric.closedBall x₀ ε := Metric.mem_closedBall_self hε.le
  have hF'x : Continuous (F' x₀) :=
    hF'c.comp_continuous (f := fun y : Γ => (x₀, y)) (continuous_const.prodMk continuous_id) fun y => ⟨hxB, trivial⟩
  have hFd : ∀ x ∈ U, ∀ y, HasFDerivAt (fun x' => L (K x' (v y)) (φ y)) (F' x y) x := by
    intro x hx y
    have hd : DifferentiableAt ℝ (Function.uncurry K) (x, v y) :=
      (hK.smooth.contDiffAt (ho.mem_nhds ⟨hx, hvU y⟩)).differentiableAt (by simp)
    have h1 : HasFDerivAt (fun x' => K x' (v y)) (D1 K x (v y)) x :=
      HasFDerivAt.comp (g := Function.uncurry K) (f := fun e => (e, v y)) x hd.hasFDerivAt
        (hasFDerivAt_prodMk_left x (v y))
    have h2 := ((L.flip (φ y)).hasFDerivAt).comp x h1
    convert h2 using 1
    · ext w; rfl
    · ext w; rfl
  have hcont : ∀ x ∈ U, Continuous fun y => L (K x (v y)) (φ y) := by
    intro x hx
    have hs : ContinuousOn (fun y => K x y) U :=
      hK.smooth.continuousOn.comp (f := fun y => (x, y)) (continuous_const.prodMk continuous_id).continuousOn
        fun y hy => ⟨hx, hy⟩
    exact (L.continuous.comp (hs.comp_continuous hv hvU)).clm_apply hφ
  have hint0 : Integrable (fun y => L (K x₀ (v y)) (φ y)) μ := by
    refine (hcont x₀ hx₀).integrable_of_hasCompactSupport (HasCompactSupport.intro (hlc (R + l x₀)) fun y hy => ?_)
    rw [hR x₀ hx₀ (v y) (hvU y) (not_le.1 hy), map_zero, ContinuousLinearMap.zero_apply]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.closedBall_mem_nhds _ hε)
    (Filter.eventually_of_mem (hU.mem_nhds hx₀) fun x hx => (hcont x hx).aestronglyMeasurable) hint0
    hF'x.aestronglyMeasurable (ae_of_all _ hb) hbi (ae_of_all _ fun y x hx => hFd x (hB hx) y)

include hU hl hv hvU hlc hφ in
theorem contDiffOn_Iop_nat (m : ℕ) : ∀ {A W : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] (L : A →L[ℝ] B →L[ℝ] W) {K : H → H → A}, Good U l K →
    ContDiffOn ℝ m (fun x => ∫ y, L (K x (v y)) (φ y) ∂μ) U := by
  induction m with
  | zero =>
    intro A W _ _ _ _ _ L K hK
    exact contDiffOn_zero.2 fun x hx =>
      (hasFDerivAt_Iop hU hl μ hv hvU hlc hφ L hK hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro A W _ _ _ _ _ L K hK
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_Iop hU hl μ hv hvU hlc hφ L hK hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact (ih (L.precompL H) (hK.d1 hU hl)).congr fun x hx => (hasFDerivAt_Iop hU hl μ hv hvU hlc hφ L hK hx).fderiv

include hU hl hv hvU hlc hφ in
theorem contDiffOn_Iop {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (L : A →L[ℝ] B →L[ℝ] W) {K : H → H → A} (hK : Good U l K) :
    ContDiffOn ℝ ∞ (fun x => ∫ y, L (K x (v y)) (φ y) ∂μ) U :=
  contDiffOn_infty.2 fun m => contDiffOn_Iop_nat hU hl μ hv hvU hlc hφ m L hK

end Gen

section Act

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem act_contDiffOn (M : KMod n)
    {k : Mat n → (M.V →L[ℂ] M.V)} (hk : ContDiffOn ℝ ∞ k (GLs n)) {R : ℝ} (hR : ∀ y ∈ GLs n, R < lg y → k y = 0)
    {F : Mat n → M.V} (hF : ContinuousOn F (GLs n)) : ContDiffOn ℝ ∞ (act μ M k F) (GLs n) := by
  haveI : ProperSpace (Mat n) := inferInstanceAs (ProperSpace (Fin n → Fin n → ℂ))
  have hL := GlobalTheory.T.length_function_facts_hold
  have hCl := GlobalTheory.CompanionTheory.WaveK.Word.cl_kK hL hk hR
  have hG : Good (GLs n) lg (GlobalTheory.CompanionTheory.WaveK.Word.kK k) := ⟨hCl.smooth, hCl.supp⟩
  have hv : Continuous (fun y : G n => (y.val : Mat n)) := Units.continuous_val
  have h := contDiffOn_Iop (Γ := G n) GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs ((hL n).2.2.2.1.continuousOn) μ hv
    val_mem_GLs (hL n).2.2.2.2.1 (hF.comp_continuous hv val_mem_GLs)
    (ContinuousLinearMap.restrictScalarsL ℂ M.V M.V ℝ ℝ) hG
  exact h.congr fun x hx => GlobalTheory.CompanionTheory.WaveK.Word.act_eq_Iop M k F hx

theorem act_mem_CE (M : KMod n)
    {k : Mat n → (M.V →L[ℂ] M.V)} (hk : ContDiffOn ℝ ∞ k (GLs n)) {R : ℝ} (hR : ∀ y ∈ GLs n, R < lg y → k y = 0)
    (hkq : ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y) = M.ρ k₁ * k y)
    {F : Mat n → M.V} (hF : ContinuousOn F (GLs n)) : act μ M k F ∈ CE M :=
  ⟨act_contDiffOn μ M hk hR hF, (GlobalTheory.T.kernel_action_equivariant GlobalTheory.T.length_function_facts_hold n μ M k F ⟨hk.continuousOn, R, hR⟩ hF hkq).2⟩

section Clm

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem Rd_clm (T : V →L[ℂ] W) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X fun x => T (f x)) (fun x => T (Rd X f x)) (GLs n) := by
  intro g hg
  have hd := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hg).hasFDerivAt
  have h : HasFDerivAt (fun x => T (f x)) ((T.restrictScalars ℝ).comp (fderiv ℝ f g)) g :=
    (T.restrictScalars ℝ).hasFDerivAt.comp g hd
  show fderiv ℝ (fun x => T (f x)) g (g * X) = _
  rw [h.fderiv]
  rfl

theorem Eu_clm (T : V →L[ℂ] W) (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Eu s a b fun x => T (f x)) (fun x => T (Eu s a b f x)) (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_clm T _ hf hg, map_smul, map_add]

theorem Epow_clm (T : V →L[ℂ] W) (s : Bool) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b fun x => T (f x)) (fun x => T (Epow s m a b f x)) (GLs n) := by
  induction m with
  | zero =>
    intro a b x _
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_clm T s a c (GlobalTheory.CompanionTheory.WaveAll.Epow_smooth GlobalTheory.T.right_derivative_calculus_holds hf s m c b) hx

theorem gel_clm (T : V →L[ℂ] W) (s : Bool) (m : ℕ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {x : Mat n}
    (hx : x ∈ GLs n) : gel s m (fun x => T (f x)) x = T (gel s m f x) := by
  simp only [gel, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_clm T s hf m a a hx

end Clm

section Mult

variable {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)} {val : Inf n → ℂ} {T : ℝ}

theorem mult_contDiffOn (h : IsMult μ M k val T) : ContDiffOn ℝ ∞ k (GLs n) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  exact (ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)).congr fun y hy => hk y hy

theorem mult_left_equivariant (h : IsMult μ M k val T) :
    ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y) = M.ρ k₁ * k y := by
  intro y hy k₁
  have e := mult_equivariant h y hy k₁ 1
  simpa using e

theorem act_contDiffOn_of_mult (h : IsMult μ M k val T) {F : Mat n → M.V} (hF : ContinuousOn F (GLs n)) :
    ContDiffOn ℝ ∞ (act μ M k F) (GLs n) := by
  obtain ⟨R, hR⟩ := mult_exists_lg h
  exact act_contDiffOn μ M (mult_contDiffOn μ h) hR hF

theorem act_mem_CE_of_mult (h : IsMult μ M k val T) {F : Mat n → M.V} (hF : ContinuousOn F (GLs n)) :
    act μ M k F ∈ CE M := by
  obtain ⟨R, hR⟩ := mult_exists_lg h
  exact act_mem_CE μ M (mult_contDiffOn μ h) hR (mult_left_equivariant μ h) hF

omit [BorelSpace (G n)] [μ.IsHaarMeasure] in
theorem isMult_of_isKer {w : List (Bool × ℕ)} {g : ℝ → ℝ} (hg : IsBump g T) (hk : IsKer μ M w g k) :
    IsMult μ M k (fun χ => zVal w χ * coshT g (cas χ)) T :=
  ⟨1, fun _ => 1, fun _ => w, fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, fun y _ => by simp, fun χ => by simp⟩

theorem act_congr_GLs {F F' : Mat n → M.V} (h : Set.EqOn F F' (GLs n)) {x : Mat n} (hx : x ∈ GLs n) :
    act μ M k F x = act μ M k F' x := by
  unfold act
  exact integral_congr_ae (ae_of_all _ fun t => by
    show k t.val (F (x * t.val)) = k t.val (F' (x * t.val))
    rw [h (GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx (val_mem_GLs t))])

theorem gel_eigen_of_act (hW : WaveEx) {k' : Mat n → (M.V →L[ℂ] M.V)} {g : ℝ → ℝ} {s : Bool} {m : ℕ}
    (hk : IsKer μ M [] g k) (hk' : IsKer μ M [(s, m)] g k') (hkm : IsMult μ M k val T) {F : Mat n → M.V}
    (hF : F ∈ CE M) (hFc : ContinuousOn F (GLs n)) (e : M.V) {A : Mat n → ℂ} {c c' : ℂ} (hc : c ≠ 0)
    (hA : ∀ x ∈ GLs n, c * A x = ⟪e, act μ M k F x⟫_ℂ) (hA' : ∀ x ∈ GLs n, c' * A x = ⟪e, act μ M k' F x⟫_ℂ)
    {x : Mat n} (hx : x ∈ GLs n) : gel s m A x = (c' / c) • A x := by
  obtain ⟨u, hu, hu0⟩ := hW n M F hF
  have hZ : ContDiffOn ℝ ∞ (act μ M k F) (GLs n) := act_contDiffOn_of_mult μ hkm hFc
  have hu0' : Set.EqOn (u 0) F (GLs n) := fun x hx => hu0 x hx
  have hYZ : Set.EqOn (fun x => ∫ t, (g t : ℂ) • u t x) (act μ M k F) (GLs n) := fun x hx => by
    have h := hk.2.2.2 u hu x hx
    rw [act_congr_GLs μ hu0' hx] at h
    exact h.symm
  have hgel : act μ M k' F x = gel s m (fun x => ∫ t, (g t : ℂ) • u t x) x := by
    have h := hk'.2.2.2 u hu x hx
    rw [act_congr_GLs μ hu0' hx] at h
    exact h
  have hAs : ContDiffOn ℝ ∞ A (GLs n) := by
    have h1 : ContDiffOn ℝ ∞ (fun x => c⁻¹ * ⟪e, act μ M k F x⟫_ℂ) (GLs n) :=
      contDiffOn_const.mul (((innerSL ℂ e).restrictScalars ℝ).contDiff.comp_contDiffOn hZ)
    refine h1.congr fun y hy => ?_
    rw [← hA y hy, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have h2 : gel s m (fun x => ⟪e, act μ M k F x⟫_ℂ) x = ⟪e, gel s m (act μ M k F) x⟫_ℂ :=
    gel_clm (innerSL ℂ e) s m hZ hx
  have h3 : gel s m (fun x => ⟪e, act μ M k F x⟫_ℂ) x = gel s m (fun x => c * A x) x :=
    GlobalTheory.CompanionTheory.WaveAll.gel_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (fun y hy => (hA y hy).symm) s m hx
  have h4 : gel s m (fun x => c * A x) x = c * gel s m A x := by
    have e1 : (fun x => c * A x) = fun x => (c • ContinuousLinearMap.id ℂ ℂ) (A x) := by
      funext y; simp
    rw [e1, gel_clm _ s m hAs hx]
    simp
  have h5 : c' * A x = c * gel s m A x := by
    rw [hA' x hx, hgel, GlobalTheory.CompanionTheory.WaveAll.gel_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hYZ s m hx, ← h2, h3, h4]
  rw [smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hc]
  linear_combination (-1 : ℂ) * h5

end Mult

end Act

end GelP

end PositivityTheory.Rg.BcB.CG

end
