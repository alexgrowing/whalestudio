import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped Classical
open scoped SchwartzMap ContDiff Topology

namespace UpperTheory.V.Z.Inf

section Abs

variable {P α V ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [MeasurableSpace α] {ν : Measure α}
  [IsFiniteMeasure ν] [Fintype ι] {U : Set P} {D : ι → V → V} {f : V → P → α → ℂ} {A : ι → P → P →L[ℝ] ℝ}

private theorem abs_deriv (hU : IsOpen U) (hA : ∀ b, ContinuousOn (A b) U)
    (hm : ∀ v, ∀ y ∈ U, AEStronglyMeasurable (f v y) ν) (hb : ∀ v, ∃ C, ∀ y ∈ U, ∀ x, ‖f v y x‖ ≤ C)
    (hd : ∀ v x, ∀ y ∈ U, HasFDerivAt (fun y => f v y x) (∑ b, (A b y).smulRight (f (D b v) y x)) y)
    (v : V) {y : P} (hy : y ∈ U) :
    HasFDerivAt (fun y => ∫ x, f v y x ∂ν) (∑ b, (A b y).smulRight (∫ x, f (D b v) y x ∂ν)) y := by
  choose C hC using hb
  have hi : ∀ w, Integrable (f w y) ν := fun w =>
    Integrable.of_bound (hm w y hy) (C w) (Filter.Eventually.of_forall (hC w y hy))
  have hs : {z | z ∈ U ∧ ∀ b, ‖A b z‖ < ‖A b y‖ + 1} ∈ 𝓝 y := by
    refine Filter.inter_mem (hU.mem_nhds hy) (Filter.eventually_all.2 fun b => ?_)
    exact ((hA b).continuousAt (hU.mem_nhds hy)).norm.eventually (gt_mem_nhds (lt_add_one _))
  have hL : ∀ b, Integrable (fun x => (A b y).smulRight (f (D b v) y x)) ν := fun b =>
    (ContinuousLinearMap.smulRightL ℝ P ℂ (A b y)).integrable_comp (hi _)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := ν) (F := f v)
    (F' := fun z x => ∑ b, (A b z).smulRight (f (D b v) z x))
    (bound := fun _ => ∑ b, (‖A b y‖ + 1) * C (D b v)) hs
    (Filter.eventually_of_mem (hU.mem_nhds hy) (hm v)) (hi v)
    (integrable_finset_sum _ fun b _ => hL b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x z hz => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul (hz.2 b).le (hC _ z hz.1 x) (norm_nonneg _) (by positivity)))
    (integrable_const _) (Filter.Eventually.of_forall fun x z hz => hd v x z hz.1)
  rw [integral_finset_sum _ fun b _ => hL b] at key
  refine key.congr_fderiv (Finset.sum_congr rfl fun b _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ P ℂ (A b y)).integral_comp_comm (hi _))

private theorem abs_smooth {G : V → P → ℂ} (hU : IsOpen U) (hA : ∀ b, ContDiffOn ℝ ∞ (A b) U)
    (hd : ∀ v, ∀ y ∈ U, HasFDerivAt (G v) (∑ b, (A b y).smulRight (G (D b v) y)) y) (v : V) :
    ContDiffOn ℝ ∞ (G v) U := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing v with
  | zero => exact contDiffOn_zero.2 fun y hy => (hd v y hy).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn]
    refine ⟨fun h => by simp at h, fun y => ∑ b, (A b y).smulRight (G (D b v) y), ?_,
      fun y hy => (hd v y hy).hasFDerivWithinAt⟩
    exact ContDiffOn.sum fun b _ => ((hA b).of_le (by exact_mod_cast le_top)).smulRight (ih _)

end Abs

section Con

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

private def lm (K : Type) [Field K] [NumberField K] (n : ℕ) : Lie K n →L[ℝ] Lie K n →L[ℝ] Lie K n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => LinearMap.toContinuousLinearMap
        { toFun := fun X => rmul X y
          map_add' := fun X Y => Matrix.mul_add (Matrix.of y) (Matrix.of X) (Matrix.of Y)
          map_smul' := fun c X => Matrix.mul_smul (Matrix.of y) c (Matrix.of X) }
      map_add' := fun y z => ContinuousLinearMap.ext fun X => map_add (rmul X) y z
      map_smul' := fun c y => ContinuousLinearMap.ext fun X => map_smul (rmul X) c y }

omit [IsTotallyComplex K] in
private theorem lm_equiv {y : Lie K n} (hy : y ∈ invSet K n) : ∃ e : Lie K n ≃L[ℝ] Lie K n, (e : Lie K n →L[ℝ] Lie K n) = lm K n y := by
  obtain ⟨u, hu⟩ := hy
  obtain rfl : y = toL u.val := hu.symm
  exact ⟨ContinuousLinearEquiv.equivOfInverse (lm K n (toL u.val)) (lm K n (toL (u⁻¹).val))
    (fun X => u.inv_mul_cancel_left (Matrix.of X)) (fun X => u.mul_inv_cancel_left (Matrix.of X)), rfl⟩

private def cf (K : Type) [Field K] [NumberField K] (n : ℕ) (b : Fin (Module.finrank ℝ (Lie K n))) (y : Lie K n) : Lie K n →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie K n)).coord b)).comp (lm K n y).inverse

omit [IsTotallyComplex K] in
private theorem cf_smooth (b : Fin (Module.finrank ℝ (Lie K n))) : ContDiffOn ℝ ∞ (cf K n b) (invSet K n) := by
  intro y hy
  obtain ⟨e, he⟩ := lm_equiv hy
  have h1 : ContDiffAt ℝ ∞ (fun z => (lm K n z).inverse) y :=
    ContDiffAt.comp y (g := ContinuousLinearMap.inverse) (he ▸ contDiffAt_map_inverse e) (lm K n).contDiff.contDiffAt
  exact (contDiffAt_const.clm_comp h1).contDiffWithinAt

private theorem chart_deriv (φ : Sm K n) (g : GA K n) {y : Lie K n} (hy : y ∈ invSet K n) :
    HasFDerivAt (chart φ.1 g) (∑ b, (cf K n b y).smulRight (chart (lie K n (Module.finBasis ℝ (Lie K n) b) φ).1 g y)) y := by
  have h := (((φ.2 g).contDiffAt (isOpen_invSet.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  refine h.congr_fderiv (Eq.symm ?_)
  obtain ⟨e, he⟩ := lm_equiv hy
  ext1 Z
  obtain ⟨X, rfl⟩ := e.surjective Z
  have e1 : ∀ Y, chart (lie K n Y φ).1 g y = fderiv ℝ (chart φ.1 g) y (e Y) := fun Y => by
    have : e Y = rmul Y y := congrArg (fun L : Lie K n →L[ℝ] Lie K n => L Y) he
    rw [this]
    exact chart_lieD φ.2 Y g hy
  have e2 : ∀ b, cf K n b y (e X) = (Module.finBasis ℝ (Lie K n)).repr X b := fun b => by
    simp [cf, ← he]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, e1, e2, ← map_smul, ← map_sum,
    Module.Basis.sum_repr]

omit [IsTotallyComplex K] in
private theorem cf_one (b : Fin (Module.finrank ℝ (Lie K n))) (X : Lie K n) :
    cf K n b (oneL K n) X = (Module.finBasis ℝ (Lie K n)).repr X b := by
  have : lm K n (oneL K n) = ContinuousLinearMap.id ℝ _ := ContinuousLinearMap.ext fun X => Matrix.one_mul (Matrix.of X)
  simp [cf, this]

end Con

section Main

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

private theorem cusp_facts (hn : 1 ≤ n) {σ : CuspSub K n} (h : Cm.carrier σ ≤ centralCuspForms K n) (φ : σ.V) :
    Continuous φ.1.1 ∧ ∃ C, ∀ y, ‖φ.1.1 y‖ ≤ C := by
  obtain ⟨ψ, rfl⟩ := (Cm.carrierEq σ).surjective φ
  exact ⟨ψ.1.2.1.continuous, exists_norm_le_of_cusp hn ψ.1.2 (h ψ.2)⟩

private theorem coef_deriv (hn : 1 ≤ n) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure] {σ : CuspSub K n}
    (h : Cm.carrier σ ≤ centralCuspForms K n) (φ₂ : cuspForms K n) (g : GA K n) (φ : σ.V) {y : Lie K n}
    (hy : y ∈ invSet K n) :
    HasFDerivAt (chart (GJGlobal.matrixCoeff μ φ.1.1 φ₂.1) g) (∑ b, (cf K n b y).smulRight
      (chart (GJGlobal.matrixCoeff μ (σ.op (.lie (Module.finBasis ℝ (Lie K n) b)) φ).1.1 φ₂.1) g y)) y := by
  have : IsFiniteMeasure (μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n))) :=
    isFiniteMeasure_restrict.2 (GJGlobal.measure_fundamentalDomain_rationalGLOne_lt_top μ).ne
  obtain ⟨C₂, hC₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ₂.2
  have h2c : Continuous φ₂.1 := φ₂.2.1.continuous
  let f : σ.V → Lie K n → Reduction.normOneGL K n → ℂ := fun v z x =>
    chart v.1.1 ((x : AdelicGLn.AdelicGL K n) * g) z * (starRingEnd ℂ) (φ₂.1 x)
  have hf : ∀ (v : σ.V), ∀ z ∈ invSet K n, chart (GJGlobal.matrixCoeff μ v.1.1 φ₂.1) g z =
      ∫ x in RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n), f v z x ∂μ := by
    intro v z hz
    obtain ⟨u, hu⟩ := hz
    obtain rfl : z = toL u.val := hu.symm
    simp only [f, chart_val, GJGlobal.matrixCoeff, mul_assoc]
  have key := abs_deriv (ν := μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n)))
    (f := f) (D := fun b v => σ.op (.lie (Module.finBasis ℝ (Lie K n) b)) v) (A := cf K n) isOpen_invSet
    (fun b => (cf_smooth b).continuousOn) ?_ ?_ ?_ φ hy
  · simp only [hf _ y hy]
    exact key.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) (hf φ))
  · intro v z hz
    obtain ⟨u, hu⟩ := hz
    obtain rfl : z = toL u.val := hu.symm
    refine Continuous.aestronglyMeasurable ?_
    simp only [f, chart_val]
    exact ((cusp_facts hn h v).1.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)).mul
      (continuous_star.comp (h2c.comp continuous_subtype_val))
  · intro v
    obtain ⟨C, hC⟩ := (cusp_facts hn h v).2
    refine ⟨C * C₂, fun z hz x => ?_⟩
    obtain ⟨u, hu⟩ := hz
    obtain rfl : z = toL u.val := hu.symm
    simp only [f, chart_val]
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _ x.2) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))
  · intro v x z hz
    refine ((chart_deriv v.1 ((x : AdelicGLn.AdelicGL K n) * g) hz).mul_const _).congr_fderiv ?_
    ext1 Z
    simp only [f, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Complex.real_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm, mul_assoc]
    rfl

private theorem coef_int (hn : 1 ≤ n) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure] {σ : CuspSub K n}
    (h : Cm.carrier σ ≤ centralCuspForms K n) (φ₂ : cuspForms K n) (g : GA K n) (φ : σ.V) :
    Integrable (fun x : Reduction.normOneGL K n => φ.1.1 ((x : AdelicGLn.AdelicGL K n) * g) * (starRingEnd ℂ) (φ₂.1 x))
      (μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n))) := by
  have : IsFiniteMeasure (μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n))) :=
    isFiniteMeasure_restrict.2 (GJGlobal.measure_fundamentalDomain_rationalGLOne_lt_top μ).ne
  obtain ⟨C₂, hC₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ₂.2
  have h2c : Continuous φ₂.1 := φ₂.2.1.continuous
  obtain ⟨hc, C, hC⟩ := cusp_facts hn h φ
  refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) (C * C₂) (Filter.Eventually.of_forall fun x => ?_)
  · exact (hc.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_star.comp (h2c.comp continuous_subtype_val))
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _ x.2) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

private def coefMap (hn : 1 ≤ n) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure] {σ : CuspSub K n}
    (h : Cm.carrier σ ≤ centralCuspForms K n) (φ₂ : cuspForms K n) : σ.V →ₗ[ℂ] Sm K n where
  toFun φ := ⟨GJGlobal.matrixCoeff μ φ.1.1 φ₂.1, fun g =>
    abs_smooth (G := fun v : σ.V => chart (GJGlobal.matrixCoeff μ v.1.1 φ₂.1) g) isOpen_invSet cf_smooth
      (fun v _ hy => coef_deriv hn μ h φ₂ g v hy) φ⟩
  map_add' φ ψ := Subtype.ext (funext fun g => by
    refine Eq.trans ?_ (integral_add (coef_int hn μ h φ₂ g φ) (coef_int hn μ h φ₂ g ψ))
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => add_mul _ _ _))
  map_smul' c φ := Subtype.ext (funext fun g => by
    refine Eq.trans ?_ (integral_const_mul c _)
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_assoc _ _ _))

private theorem coefMap_lie (hn : 1 ≤ n) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure] {σ : CuspSub K n}
    (h : Cm.carrier σ ≤ centralCuspForms K n) (φ₂ : cuspForms K n) (X : Lie K n) (φ : σ.V) :
    coefMap hn μ h φ₂ (σ.op (.lie X) φ) = lie K n X (coefMap hn μ h φ₂ φ) := by
  have e : σ.op (.lie X) φ = ∑ b, (((Module.finBasis ℝ (Lie K n)).repr X b : ℝ) : ℂ) •
      σ.op (.lie (Module.finBasis ℝ (Lie K n) b)) φ := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    change lie K n X φ.1 = ∑ b, (((Module.finBasis ℝ (Lie K n)).repr X b : ℝ) : ℂ) • lie K n (Module.finBasis ℝ (Lie K n) b) φ.1
    conv_lhs => rw [← (Module.finBasis ℝ (Lie K n)).sum_repr X]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Complex.coe_smul]
  refine Subtype.ext (funext fun g => ?_)
  have h1 : oneL K n ∈ invSet K n := val_mem_invSet (1 : GL (Fin n) (Cinf K))
  have hc : ∀ F : GA K n → ℂ, chart F g (oneL K n) = F g := fun F =>
    (chart_val F g 1).trans (by rw [map_one, mul_one])
  have h2 := congrArg (fun L : Lie K n →L[ℝ] ℂ => L X) (coef_deriv hn μ h φ₂ g φ h1).fderiv
  refine Eq.trans ?_ h2.symm
  simp only [e, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, cf_one, hc,
    Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rfl

private theorem cap_comm {σ : CuspSub K n} (T : σ.V →ₗ[ℂ] Sm K n)
    (hT : ∀ X φ, T (σ.op (.lie X) φ) = lie K n X (T φ)) (τ : K →+* ℂ) (u : ℂ) (φ φ' : σ.V)
    (e : φ'.1 = cap τ u φ.1) : T φ' = cap τ u (T φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm K n)) :=
    { carrier := {z | ∀ ψ : σ.V, ∃ ψ' : σ.V, ψ'.1 = z ψ.1 ∧ T ψ' = z (T ψ)}
      mul_mem' := fun {x y} hx hy ψ => by
        obtain ⟨a, ha, ha'⟩ := hy ψ
        obtain ⟨b, hb, hb'⟩ := hx a
        exact ⟨b, by rw [hb, ha]; rfl, by rw [hb', ha']; rfl⟩
      add_mem' := fun {x y} hx hy ψ => by
        obtain ⟨a, ha, ha'⟩ := hx ψ
        obtain ⟨b, hb, hb'⟩ := hy ψ
        exact ⟨a + b, by rw [Submodule.coe_add, hb, ha]; rfl, by rw [map_add, hb', ha']; rfl⟩
      algebraMap_mem' := fun c ψ => ⟨c • ψ, rfl, map_smul T c ψ⟩ }
  have hl : ∀ X, lie K n X ∈ S := fun X ψ => ⟨σ.op (.lie X) ψ, rfl, hT X ψ⟩
  have hE : ∀ i j : Fin n, Eop τ i j ∈ S := fun i j => by
    have : Eop (a := n) τ i j = AlgRepEndIrreducible.eL (N := Module.End ℂ (Sm K n)) (lie K n) τ i j := rfl
    rw [this, AlgRepEndIrreducible.eL]
    exact S.smul_mem (S.sub_mem (hl _) (S.smul_mem (hl _) _)) _
  have hc : cap τ u ∈ S := by
    have := Fb.map_qdet S.val (fun i j => ⟨Eop τ i j, hE i j⟩) (u + ((n : ℂ) - 1) / 2)
    have e2 : cap τ u = Formalism.REAL.qdet (Eop (a := n) τ) (u + ((n : ℂ) - 1) / 2) := rfl
    rw [e2]
    exact (show _ = Formalism.REAL.qdet (Eop (a := n) τ) (u + ((n : ℂ) - 1) / 2) from this) ▸ Subtype.prop _
  obtain ⟨a, ha, ha'⟩ := hc φ
  rw [← ha', Subtype.ext (e.trans ha.symm)]

end Main

end UpperTheory.V.Z.Inf

theorem UpperTheory.V.Z.Inf.coefSm :
    UpperTheory.V.Z.Inf.CoefSm := by
  intro K _ _ _ n hn μ _ σ h φ₂
  exact ⟨coefMap hn μ h φ₂, fun _ => rfl, cap_comm _ (coefMap_lie hn μ h φ₂)⟩
