import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

noncomputable section

open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

def weylAlg (l : Type) [Fintype l] : Subalgebra ℂ (Sch l →L[ℂ] Sch l) := Algebra.adjoin ℂ (Set.range dRho)

theorem dRho_mem_weylAlg (w : l ⊕ l → ℝ) : dRho w ∈ weylAlg l := Algebra.subset_adjoin ⟨w, rfl⟩

theorem weylAlg_induction {P : (Sch l →L[ℂ] Sch l) → Prop} (h1 : P 1)
    (hmul : ∀ A w, P A → P (A * dRho w)) (h0 : P 0) (hadd : ∀ A B, P A → P B → P (A + B))
    (hsmul : ∀ (c : ℂ) A, P A → P (c • A)) {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l) : P A := by
  have h : A ∈ Submodule.span ℂ (Submonoid.closure (Set.range (dRho (l := l))) : Set (Sch l →L[ℂ] Sch l)) := by
    rw [← Algebra.adjoin_eq_span]; exact hA
  refine Submodule.span_induction (p := fun A _ => P A) (fun B hB => ?_) h0 (fun A B _ _ => hadd A B)
    (fun c A _ => hsmul c A) h
  refine Submonoid.closure_induction_right (motive := fun A _ => P A) h1 ?_ hB
  rintro A _ _ ⟨w, rfl⟩ hA
  exact hmul A w hA

theorem lineDeriv_mem_weylAlg (v : EuclideanSpace ℝ l) : lineDerivOpCLM ℂ (Sch l) v ∈ weylAlg l := by
  have : lineDerivOpCLM ℂ (Sch l) v = dRho (Sum.elim (fun i => v i) 0) := by
    ext f x
    have h1 : pPart (Sum.elim (fun i => v i) 0 : l ⊕ l → ℝ) = v := rfl
    have h2 : qPart (Sum.elim (fun i => v i) 0 : l ⊕ l → ℝ) = 0 := rfl
    simp [dRho_apply, h1, h2, lineDerivOp_apply_eq_fderiv]
  rw [this]; exact dRho_mem_weylAlg _

theorem iteratedLineDeriv_mem_weylAlg {n : ℕ} (m : Fin n → EuclideanSpace ℝ l) :
    iteratedLineDerivOpCLM ℂ (Sch l) m ∈ weylAlg l := by
  induction n with
  | zero =>
    have : iteratedLineDerivOpCLM ℂ (Sch l) m = 1 := by
      ext1 f; simp
    rw [this]; exact one_mem _
  | succ n ih =>
    have : iteratedLineDerivOpCLM ℂ (Sch l) m =
        lineDerivOpCLM ℂ (Sch l) (m 0) * iteratedLineDerivOpCLM ℂ (Sch l) (Fin.tail m) := by
      ext1 f; simp [iteratedLineDerivOp_succ_left]
    rw [this]; exact mul_mem (lineDeriv_mem_weylAlg _) (ih _)

variable [DecidableEq l]

def weightOp (l : Type) [Fintype l] [DecidableEq l] : Sch l →L[ℂ] Sch l :=
  1 - ((4 * π ^ 2 : ℝ) : ℂ)⁻¹ • ∑ j : l, dRho (Pi.single (Sum.inr j) 1) * dRho (Pi.single (Sum.inr j) 1)

def besselOp (l : Type) [Fintype l] [DecidableEq l] : Sch l →L[ℂ] Sch l :=
  1 - ((4 * π ^ 2 : ℝ) : ℂ)⁻¹ • ∑ j : l, dRho (Pi.single (Sum.inl j) 1) * dRho (Pi.single (Sum.inl j) 1)

theorem weightOp_mem : weightOp l ∈ weylAlg l :=
  sub_mem (one_mem _) (Subalgebra.smul_mem _ (sum_mem fun _ _ => mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) _)

theorem besselOp_mem : besselOp l ∈ weylAlg l :=
  sub_mem (one_mem _) (Subalgebra.smul_mem _ (sum_mem fun _ _ => mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) _)

theorem weightOp_apply (f : Sch l) (x : EuclideanSpace ℝ l) :
    weightOp l f x = ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) * f x := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [weightOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
    SchwartzMap.sum_apply, dRho_single_inr, smul_eq_mul, EuclideanSpace.real_norm_sq_eq]
  push_cast
  rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  rw [I_sq]
  ring

theorem weightOp_pow_apply (k : ℕ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    (weightOp l ^ k) f x = (((1 + ‖x‖ ^ 2) ^ k : ℝ) : ℂ) * f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, weightOp_apply, ih]
    push_cast
    ring

theorem norm_weightOp_pow_apply (k : ℕ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    ‖(weightOp l ^ k) f x‖ = (1 + ‖x‖ ^ 2) ^ k * ‖f x‖ := by
  rw [weightOp_pow_apply, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)]

theorem fourierInv_dRho_inl (j : l) (f : Sch l) :
    𝓕⁻ (dRho (Pi.single (Sum.inl j) 1) f) = -dRho (Pi.single (Sum.inr j) 1) (𝓕⁻ f) := by
  rw [dRho_single_inl, fourierInv_lineDerivOp_eq]
  ext x
  have : (fun y : EuclideanSpace ℝ l => y j).HasTemperateGrowth :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasTemperateGrowth
  simp [dRho_single_inr, EuclideanSpace.inner_single_right, this, mul_assoc]

theorem fourierInv_besselOp (f : Sch l) : 𝓕⁻ (besselOp l f) = weightOp l (𝓕⁻ f) := by
  let F : Sch l →L[ℂ] Sch l := FourierTransform.fourierInvCLM ℂ (Sch l)
  have hF : ∀ g : Sch l, 𝓕⁻ g = F g := fun _ => rfl
  have h := fourierInv_dRho_inl (l := l)
  simp only [hF] at h ⊢
  simp only [besselOp, weightOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul,
    map_sum, h, map_neg, neg_neg]

theorem fourierInv_besselOp_pow (k : ℕ) (f : Sch l) : 𝓕⁻ ((besselOp l ^ k) f) = (weightOp l ^ k) (𝓕⁻ f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, fourierInv_besselOp, ih]

theorem exists_norm_toLp_one_le :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f : Sch l, ‖f.toLp 1 volume‖ ≤ C * ‖((weightOp l ^ N) f).toLp 2 volume‖ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  let u : EuclideanSpace ℝ l → ℂ := fun x => ((((1 + ‖x‖ ^ 2) ^ N)⁻¹ : ℝ) : ℂ)
  have hun : ∀ x, ‖u x‖ = ((1 + ‖x‖ ^ 2) ^ N)⁻¹ := fun x => by
    simp only [u]
    rw [norm_real, Real.norm_of_nonneg (by positivity)]
  have hc : Continuous u := by
    refine continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) fun x => by positivity)
  have hu : MemLp u (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp, memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
    have := integrable_rpow_neg_one_add_norm_sq (E := EuclideanSpace ℝ l) (μ := volume) (r := 4 * N)
      (by rw [hN]; push_cast; have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EuclideanSpace ℝ l)); linarith)
    refine this.congr (.of_forall fun x => ?_)
    simp only [hun]
    rw [show -(4 * (N : ℝ)) / 2 = -((N * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by positivity),
      Real.rpow_natCast, pow_mul, inv_pow]
  refine ⟨N, (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ),
    Real.rpow_nonneg (integral_nonneg fun x => by positivity) _, fun f => ?_⟩
  have := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu (((weightOp l ^ N) f).memLp _ volume)
  rw [norm_toLp_one, norm_toLp' (by simp) (by simp)]
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by simp)))
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [hun, norm_weightOp_pow_apply]
  field_simp

theorem exists_norm_apply_le :
    ∃ A ∈ weylAlg l, ∀ (f : Sch l) (x : EuclideanSpace ℝ l), ‖f x‖ ≤ ‖(A f).toLp 2 volume‖ := by
  obtain ⟨N, C, hC, h⟩ := exists_norm_toLp_one_le (l := l)
  refine ⟨(C : ℂ) • besselOp l ^ N, Subalgebra.smul_mem _ (pow_mem besselOp_mem _) _, fun f x => ?_⟩
  have h1 := norm_fourier_apply_le_toLp_one (𝓕⁻ f) x
  rw [FourierTransform.fourier_fourierInv_eq] at h1
  refine h1.trans ((h _).trans (le_of_eq ?_))
  rw [← fourierInv_besselOp_pow, ← norm_fourier_toL2_eq, FourierTransform.fourier_fourierInv_eq,
    ContinuousLinearMap.smul_apply, ← toLpCLM_apply (𝕜 := ℂ), ← toLpCLM_apply (𝕜 := ℂ), map_smul, norm_smul,
    norm_real, Real.norm_of_nonneg hC]

theorem norm_multilinear_le {n : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ l) ℂ) :
    ‖m‖ ≤ ∑ r : Fin n → l, ‖m fun i => EuclideanSpace.single (r i) 1‖ := by
  refine m.opNorm_le_bound (by positivity) fun v => ?_
  have : v = fun i => ∑ j, v i j • (EuclideanSpace.single j 1 : EuclideanSpace ℝ l) := by
    funext i
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [this, m.map_sum]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [m.map_smul_univ, norm_smul, mul_comm, norm_prod]
  gcongr with i
  exact PiLp.norm_apply_le _ _

theorem exists_seminorm_le (k n : ℕ) :
    ∃ A : (Fin n → l) → (Sch l →L[ℂ] Sch l), (∀ r, A r ∈ weylAlg l) ∧
      ∀ f : Sch l, SchwartzMap.seminorm ℂ k n f ≤ ∑ r, ‖(A r f).toLp 2 volume‖ := by
  obtain ⟨A, hA, h⟩ := exists_norm_apply_le (l := l)
  refine ⟨fun r => A * weightOp l ^ k * iteratedLineDerivOpCLM ℂ (Sch l) fun i => EuclideanSpace.single (r i) 1,
    fun r => mul_mem (mul_mem hA (pow_mem weightOp_mem _)) (iteratedLineDeriv_mem_weylAlg _), fun f => ?_⟩
  refine seminorm_le_bound ℂ k n f (by positivity) fun x => ?_
  refine (mul_le_mul_of_nonneg_left (norm_multilinear_le _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => le_trans ?_ (h _ x)
  refine le_trans ?_ (norm_weightOp_pow_apply k
    (iteratedLineDerivOpCLM ℂ (Sch l) (fun i => EuclideanSpace.single (r i) 1) f) x).ge
  rw [iteratedLineDerivOpCLM_apply, iteratedLineDerivOp_eq_iteratedFDeriv]
  gcongr
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

theorem exists_extension_of_bound {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : V →ₗ[ℂ] E) (lam : V →ₗ[ℂ] ℂ) (C : ℝ) (hb : ∀ f, ‖lam f‖ ≤ C * ‖T f‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ f, lam f = Λ (T f) := by
  have hker : LinearMap.ker T ≤ LinearMap.ker lam := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let φ : LinearMap.range T →ₗ[ℂ] ℂ := ((LinearMap.ker T).liftQ lam hker) ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ f, φ ⟨T f, f, rfl⟩ = lam f := fun f => by
    change (LinearMap.ker T).liftQ lam hker (T.quotKerEquivRange.symm ⟨T f, LinearMap.mem_range_self T f⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) (φ.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [hφ]
    exact hb f))
  refine ⟨Λ, fun f => ?_⟩
  rw [← hφ]
  exact (hΛ ⟨T f, f, rfl⟩).symm

def schwartzToL2 (l : Type) [Fintype l] : Sch l →L[ℂ] L2 l := toLpCLM ℂ ℂ 2 volume

omit [DecidableEq l] in
theorem schwartzToL2_apply (f : Sch l) : schwartzToL2 l f = f.toLp 2 volume := rfl

theorem exists_norm_le_sum (lam : Sch l →L[ℂ] ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (A : ι → (Sch l →L[ℂ] Sch l)) (C : ℝ), 0 ≤ C ∧
      (∀ i, A i ∈ weylAlg l) ∧ ∀ f, ‖lam f‖ ≤ C * ∑ i, ‖schwartzToL2 l (A i f)‖ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ)
    ((normSeminorm ℂ ℂ).comp lam.toLinearMap) (continuous_norm.comp lam.continuous)
  have hC' : ∀ f, ‖lam f‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ l) ℂ) f := fun f => hC f
  clear hC
  choose A hA hA' using exists_seminorm_le (l := l)
  simp only [← schwartzToL2_apply] at hA'
  refine ⟨Σ p : s, (Fin p.1.2 → l), inferInstance, fun i => A i.1.1.1 i.1.1.2 i.2, C, C.2, fun i => hA _ _ _,
    fun f => (hC' f).trans (mul_le_mul_of_nonneg_left ?_ C.2)⟩
  rw [Fintype.sum_sigma]
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun p hp => ?_
  rw [schwartzSeminormFamily_apply]
  refine (hA' p.1 p.2 f).trans ?_
  exact Finset.single_le_sum (f := fun q : s => ∑ r, ‖schwartzToL2 l (A q.1.1 q.1.2 r f)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (⟨p, hp⟩ : s))

theorem exists_factor (lam : Sch l →L[ℂ] ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (A : ι → (Sch l →L[ℂ] Sch l)) (Λ : (ι → L2 l) →L[ℂ] ℂ),
      (∀ i, A i ∈ weylAlg l) ∧ ∀ f, lam f = Λ fun i => schwartzToL2 l (A i f) := by
  obtain ⟨ι, _, A, C, hC, hA, h⟩ := exists_norm_le_sum lam
  let T : Sch l →ₗ[ℂ] (ι → L2 l) := LinearMap.pi fun i => (schwartzToL2 l).toLinearMap ∘ₗ (A i).toLinearMap
  have hT : ∀ f, T f = fun i => schwartzToL2 l (A i f) := fun f => by
    funext i
    simp [T]
  clear_value T
  obtain ⟨Λ, hΛ⟩ := exists_extension_of_bound T lam.toLinearMap (C * Fintype.card ι) fun f => by
    refine (h f).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have h1 : ∀ i, ‖schwartzToL2 l (A i f)‖ ≤ ‖T f‖ := fun i => by
      have := norm_le_pi_norm (T f) i
      rwa [congrFun (hT f) i] at this
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    simp
  refine ⟨ι, inferInstance, A, Λ, hA, fun f => ?_⟩
  rw [← hT]
  exact hΛ f

omit [DecidableEq l] in
theorem hasDerivAt_rhoFun_at (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) (t : ℝ) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (rhoFun (t • w) (dRho w f) x) t := by
  have h1 := ((hasDerivAt_rhoFun w f (x + pPart (t • w))).const_mul (phase (t • w) x))
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h3 := HasDerivAt.scomp_of_eq (𝕜 := ℝ) (𝕜' := ℝ) t h1 h2 (by simp)
  rw [one_smul] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun s => ?_)
  have h4 := congrFun (rhoFun_rhoFun (t • w) ((s - t) • w) f) x
  have h5 : sympl (t • w) ((s - t) • w) = 0 := by
    simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (pPart w) (qPart w)]
    ring
  rw [h5, ← add_smul, add_sub_cancel] at h4
  simpa [rhoFun] using h4.symm

omit [DecidableEq l] in
theorem inner_toLp_rho (w : l ⊕ l → ℝ) (φ f : Sch l) :
    inner ℂ (φ.toLp 2 volume) (rho w (f.toLp 2 volume)) = ∫ x, inner ℂ (φ x) (rhoFun w f x) := by
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 volume, (coeFn_rho w (f.toLp 2 volume)).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))]
    with x h1 h2
  rw [h1, h2]

omit [DecidableEq l] in

theorem hasDerivAt_inner_rho (w : l ⊕ l → ℝ) (φ f : Sch l) :
    HasDerivAt (fun t : ℝ => inner ℂ (φ.toLp 2 volume) (rho (t • w) (f.toLp 2 volume)))
      (inner ℂ (φ.toLp 2 volume) ((dRho w f).toLp 2 volume)) 0 := by
  have hc : ∀ (u : l ⊕ l → ℝ) (g : Sch l), Continuous fun x => inner ℂ (φ x) (rhoFun u g x) := fun u g =>
    φ.continuous.inner ((continuous_phase u).mul (g.continuous.comp (continuous_add_const _)))
  have hb : ∀ (u : l ⊕ l → ℝ) (g : Sch l) (x), ‖inner ℂ (φ x) (rhoFun u g x)‖ ≤
      ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 g := fun u g x => by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [rhoFun, norm_mul, norm_phase, one_mul]
    exact norm_le_seminorm ℝ g _
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Set.univ) (x₀ := (0 : ℝ))
    (F := fun t x => inner ℂ (φ x) (rhoFun (t • w) f x))
    (F' := fun t x => inner ℂ (φ x) (rhoFun (t • w) (dRho w f) x))
    (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 (dRho w f)) Filter.univ_mem
    (.of_forall fun t => (hc _ _).aestronglyMeasurable)
    ((φ.integrable.norm.mul_const _).mono' (hc _ _).aestronglyMeasurable (.of_forall (hb _ f)))
    (hc _ _).aestronglyMeasurable (.of_forall fun x t _ => hb _ _ x) (φ.integrable.norm.mul_const _)
    (.of_forall fun x t _ => ((innerSL ℂ (φ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rhoFun_at w f x t))).2
  simp only [inner_toLp_rho, inner_toL2_toL2_eq]
  simpa only [zero_smul, rhoFun_zero] using this

section Metaplectic

variable {G : Type} [Group G] {pr : G →* Matrix.symplecticGroup l ℝ} {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)}
  {omS : G →* (Sch l →L[ℂ] Sch l)}

theorem omS_dRho
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (g : G) (w : l ⊕ l → ℝ) (f : Sch l) :
    omS g (dRho w f) = dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f) := by
  have key : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) ((omS g (dRho w f)).toLp 2 volume) =
      inner ℂ (φ.toLp 2 volume) ((dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f)).toLp 2 volume) := fun φ => by
    have e : ∀ v : L2 l, inner ℂ ((omS g⁻¹ φ).toLp 2 volume) v = inner ℂ (φ.toLp 2 volume) (om g v) := fun v => by
      rw [← (om g).inner_map_map, h4, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        ContinuousLinearMap.one_apply]
    have d1 := hasDerivAt_inner_rho w (omS g⁻¹ φ) f
    have d2 := hasDerivAt_inner_rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) φ (omS g f)
    simp only [e, h3, h4, mulVec_smul] at d1
    exact d1.unique d2
  apply injective_toLp 2 volume
  have := key (omS g (dRho w f) - dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f))
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem toLp_dRho_omS
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (A : Sch l →L[ℂ] Sch l) (g : G)
    (w : l ⊕ l → ℝ) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (omS g f)) = ∑ a,
      (((-(Matrix.J l ℝ * (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) a : ℂ) •
        schwartzToL2 l (A (omS g (dRho (Pi.single a 1) f))) := by
  have h1 : (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ
      ((-(Matrix.J l ℝ * (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) = w := by
    rw [mulVec_mulVec, mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      SymplecticGroup.mem_iff.1 (pr g).2, J_squared, neg_neg, one_mulVec]
  rw [ContinuousLinearMap.mul_apply]
  conv_lhs => rw [← h1, ← omS_dRho h3 h4, dRho_eq_sum]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]

theorem contDiff_toLp_omS
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → G}
    (hγ : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)
    (h5 : ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2 volume)) {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l)
    (f : Sch l) : ContDiff ℝ ∞ fun t => schwartzToL2 l (A (omS (γ t) f)) := by
  revert f
  refine weylAlg_induction (P := fun A => ∀ f, ContDiff ℝ ∞ fun t => schwartzToL2 l (A (omS (γ t) f))) ?_ ?_ ?_ ?_ ?_ hA
  · intro f
    simpa only [h4, ContinuousLinearMap.one_apply, schwartzToL2_apply] using h5 f
  · intro A w ih f
    simp only [toLp_dRho_omS h3 h4, coe_smul]
    refine ContDiff.sum fun a _ => ContDiff.fun_smul ?_ (ih _)
    simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
    exact ContDiff.sum fun b _ => ContDiff.mul (ContDiff.neg (ContDiff.sum fun c _ => ContDiff.mul
      (ContDiff.sum fun d _ => contDiff_const.mul (hγ _ _)) contDiff_const)) contDiff_const
  · intro f
    simp only [ContinuousLinearMap.zero_apply]
    exact contDiff_const
  · intro A B hA hB f
    simp only [ContinuousLinearMap.add_apply, map_add]
    exact (hA f).add (hB f)
  · intro c A hA f
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    exact (hA f).const_smul c

theorem hasDerivAt_exp_apply (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (a b : l ⊕ l) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  letI := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ a b)).hasFDerivAt.comp_hasDerivAt 0 h

theorem hasDerivAt_toLp_omS
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) {γ : ℝ → G} (h0 : γ 0 = 1)
    (hγ : ∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X))
    (h6 : ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2 volume)) ((quad X f).toLp 2 volume) 0)
    {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (A (omS (γ t) f))) (schwartzToL2 l (A (quad X f))) 0 := by
  revert f
  refine weylAlg_induction
    (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (omS (γ t) f))) (schwartzToL2 l (A (quad X f))) 0) ?_ ?_ ?_ ?_ ?_ hA
  · intro f
    simpa only [h4, ContinuousLinearMap.one_apply, schwartzToL2_apply] using h6 f
  · intro A w ih f
    simp only [toLp_dRho_omS h3 h4, hγ, coe_smul]
    have hJ : Matrix.J l ℝ * Xᵀ * Matrix.J l ℝ = X := by
      have h := mul_J_symm hX
      rw [transpose_mul, J_transpose, neg_mul, neg_eq_iff_eq_neg] at h
      rw [h, neg_mul, Matrix.mul_assoc, J_squared]
      simp
    have hd : ∀ a, HasDerivAt
        (fun t : ℝ => ((-(Matrix.J l ℝ * (NormedSpace.exp (t • X))ᵀ * Matrix.J l ℝ)) *ᵥ w) a) (-(X *ᵥ w) a) 0 := by
      intro a
      conv => enter [2]; rw [← hJ]
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply, ← Finset.sum_neg_distrib,
        ← neg_mul]
      exact HasDerivAt.fun_sum fun b _ => HasDerivAt.mul_const (HasDerivAt.fun_sum fun c _ => HasDerivAt.mul_const
        (HasDerivAt.fun_sum fun d _ => (hasDerivAt_exp_apply X _ _).const_mul _) _) _
    refine (HasDerivAt.fun_sum fun a _ => (hd a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_deriv ?_
    have e : dRho w * quad X = quad X * dRho w - dRho (X *ᵥ w) := by
      rw [← quad_comm hX, sub_sub_cancel]
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (dRho w), e, dRho_eq_sum w,
      dRho_eq_sum (X *ᵥ w)]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum,
      map_smul, ofReal_neg, ofReal_zero, zero_smul, NormedSpace.exp_zero, transpose_one, mul_one, J_squared, neg_neg, one_mulVec,
      h0, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      map_sub, neg_smul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
    simp only [coe_smul]
    rfl
  · intro f
    simp only [ContinuousLinearMap.zero_apply, map_zero]
    exact hasDerivAt_const _ _
  · intro A B hA hB f
    simp only [ContinuousLinearMap.add_apply, map_add]
    exact (hA f).add (hB f)
  · intro c A hA f
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    exact (hA f).const_smul c

theorem metaplectic_schwartz_smooth [TopologicalSpace G]
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    (h5 : ∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
      (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
      ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2 volume)) :
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : Sch l),
      omS g (dRho w f) = dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f)) ∧
    (∀ (lam : Sch l →L[ℂ] ℂ) (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
      (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
      ∀ f : Sch l, ContDiff ℝ ∞ fun t => lam (omS (γ t) f)) ∧
    (∀ (lam : Sch l →L[ℂ] ℂ), ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
      (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
      (∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2 volume)) ((quad X f).toLp 2 volume) 0) →
      ∀ f : Sch l, HasDerivAt (fun t => lam (omS (γ t) f)) (lam (quad X f)) 0) := by
  refine ⟨omS_dRho h3 h4, fun lam k γ hc hγ f => ?_, fun lam X hX γ h0 hγ h6 f => ?_⟩
  · obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
    simp only [h]
    exact (Λ.restrictScalars ℝ).contDiff.comp
      (contDiff_pi.2 fun i => contDiff_toLp_omS h3 h4 hγ (h5 k γ hc hγ) (hA i) f)
  · obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
    simp only [h]
    exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_pi.2 fun i => hasDerivAt_toLp_omS h3 h4 hX h0 hγ h6 (hA i) f)

end Metaplectic

end GlobalTheory.RealWeil

end
