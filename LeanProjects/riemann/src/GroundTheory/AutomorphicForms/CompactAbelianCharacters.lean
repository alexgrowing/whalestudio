import Mathlib
import GroundTheory.AutomorphicForms.CompactSelfAdjoint
import GroundTheory.AutomorphicForms.HilbertSchmidtCompact
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCharNeOne
set_option maxSynthPendingDepth 1

open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace GroundTheory.Automorphic.CompactAbelianFourier

noncomputable section

set_option linter.unusedSectionVars false

variable {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
  [T2Space C]

theorem exists_char_of_translate {F : C → ℂ} (hF : Continuous F) {g : C} (hg : F 1 ≠ F g)
    (htr : ∀ h : C, ∃ c : ℂ, ∀ x, F (h * x) = c * F x) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  have hF1 : F 1 ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := htr g
    have := hc 1
    rw [mul_one, h0, mul_zero] at this
    exact hg (h0.trans this.symm)
  have hmul : ∀ h x, F (h * x) = F h / F 1 * F x := by
    intro h x
    obtain ⟨c, hc⟩ := htr h
    have h1 := hc 1
    rw [mul_one] at h1
    rw [hc x, h1, mul_div_cancel_right₀ _ hF1]
  let χ₀ : C →* ℂ :=
    { toFun := fun h => F h / F 1
      map_one' := div_self hF1
      map_mul' := fun a b => by
        rw [hmul a b]
        field_simp }
  have hχc : Continuous χ₀ := hF.div_const _
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hχc.continuousOn
  have hle : ∀ h, ‖χ₀ h‖ ≤ 1 := by
    intro h
    by_contra hlt'
    have hlt := not_le.1 hlt'
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop M |>.exists
    have := hM (h ^ n) (Set.mem_univ _)
    rw [map_pow, norm_pow] at this
    linarith
  have hnorm : ∀ h, ‖χ₀ h‖ = 1 := by
    intro h
    refine le_antisymm (hle h) ?_
    have e : χ₀ h * χ₀ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg norm e
    rw [norm_mul, norm_one] at this
    nlinarith [hle h⁻¹, norm_nonneg (χ₀ h), norm_nonneg (χ₀ h⁻¹)]
  let χ : C →ₜ* Circle :=
    { toFun := fun h => ⟨χ₀ h, by simp [Submonoid.unitSphere, hnorm h]⟩
      map_one' := Subtype.ext (map_one χ₀)
      map_mul' := fun a b => Subtype.ext (map_mul χ₀ a b)
      continuous_toFun := hχc.subtype_mk fun h => by simp [Submonoid.unitSphere, hnorm h] }
  refine ⟨χ, fun h => hg ?_⟩
  have : χ₀ g = 1 := congrArg Subtype.val h
  have e : F g / F 1 = 1 := this
  rw [div_eq_one_iff_eq hF1] at e
  exact e.symm

section Metrizable

variable [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
  (μ : Measure C) [μ.IsHaarMeasure]

def transl (h : C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => h * x) (measurePreserving_mul_left μ h)).toContinuousLinearMap

theorem coeFn_transl (h : C) (f : Lp ℂ 2 μ) : transl μ h f =ᵐ[μ] fun x => f (h * x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem transl_transl (h h' : C) (f : Lp ℂ 2 μ) :
    transl μ h (transl μ h' f) = transl μ h' (transl μ h f) := by
  have e1 : (transl μ h (transl μ h' f) : C → ℂ) =ᵐ[μ] fun x => f (h' * (h * x)) := by
    filter_upwards [coeFn_transl μ h (transl μ h' f),
      (measurePreserving_mul_left μ h).quasiMeasurePreserving.ae_eq_comp (coeFn_transl μ h' f)]
      with x h1 h2
    rw [h1]
    exact h2
  have e2 : (transl μ h' (transl μ h f) : C → ℂ) =ᵐ[μ] fun x => f (h * (h' * x)) := by
    filter_upwards [coeFn_transl μ h' (transl μ h f),
      (measurePreserving_mul_left μ h').quasiMeasurePreserving.ae_eq_comp (coeFn_transl μ h f)]
      with x h1 h2
    rw [h1]
    exact h2
  refine Lp.ext (e1.trans (e2.trans (Eventually.of_forall fun x => ?_)).symm)
  simp only [mul_left_comm h h']

theorem commute_transl (h h' : C) : Commute (transl μ h) (transl μ h') :=
  ContinuousLinearMap.ext fun f => transl_transl μ h h' f

theorem inner_transl (h : C) (f g : Lp ℂ 2 μ) :
    ⟪transl μ h f, g⟫_ℂ = ⟪f, transl μ h⁻¹ g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, ⟪(transl μ h f) x, g x⟫_ℂ ∂μ = ∫ x, conj (f (h * x)) * g x ∂μ :=
    integral_congr_ae (by
      filter_upwards [coeFn_transl μ h f] with x hx
      rw [RCLike.inner_apply', hx])
  have e2 : ∫ x, ⟪f x, (transl μ h⁻¹ g) x⟫_ℂ ∂μ = ∫ x, conj (f x) * g (h⁻¹ * x) ∂μ :=
    integral_congr_ae (by
      filter_upwards [coeFn_transl μ h⁻¹ g] with x hx
      rw [RCLike.inner_apply', hx])
  rw [e1, e2, ← integral_mul_left_eq_self (fun x => conj (f x) * g (h⁻¹ * x)) h]
  simp only [inv_mul_cancel_left]

variable (ψ : C(C, ℝ))

def kerFun (p : C × C) : ℂ := (ψ (p.1 / p.2) : ℂ)

theorem continuous_kerFun : Continuous (kerFun ψ) :=
  Complex.continuous_ofReal.comp (ψ.continuous.comp (continuous_fst.div' continuous_snd))

theorem norm_kerFun_le (p : C × C) : ‖kerFun ψ p‖ ≤ ‖ψ‖ := by
  simpa [kerFun] using ψ.norm_coe_le_norm (p.1 / p.2)

theorem memLp_kerFun : MemLp (kerFun ψ) 2 (μ.prod μ) :=
  MemLp.of_bound (continuous_kerFun ψ).aestronglyMeasurable ‖ψ‖
    (Eventually.of_forall (norm_kerFun_le ψ))

def convOp : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  L2Kernel.kernelOp ((memLp_kerFun μ ψ).toLp (kerFun ψ))

theorem isCompactOperator_convOp : IsCompactOperator (convOp μ ψ) :=
  (L2Kernel.kernelOp_isHilbertSchmidt _).isCompactOperator

def rowCM : C(C, C(C, ℂ)) := ContinuousMap.curry ⟨kerFun ψ, continuous_kerFun ψ⟩

def row (x : C) : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ (rowCM ψ x)

theorem continuous_row : Continuous (row μ ψ) :=
  (ContinuousMap.toLp 2 μ ℂ).continuous.comp (rowCM ψ).continuous

def convFun (f : Lp ℂ 2 μ) : C(C, ℂ) :=
  ⟨fun x => ⟪row μ ψ x, f⟫_ℂ, (continuous_row μ ψ).inner continuous_const⟩

theorem convFun_def (f : Lp ℂ 2 μ) (x : C) : convFun μ ψ f x = ⟪row μ ψ x, f⟫_ℂ := rfl

theorem convFun_apply (f : Lp ℂ 2 μ) (x : C) :
    convFun μ ψ f x = ∫ y, (ψ (x / y) : ℂ) * f y ∂μ := by
  rw [convFun_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (rowCM ψ x)] with y hy
  rw [RCLike.inner_apply', row, hy]
  simp [rowCM, kerFun]

theorem convFun_add (f g : Lp ℂ 2 μ) : convFun μ ψ (f + g) = convFun μ ψ f + convFun μ ψ g := by
  ext x
  simp [convFun_def, inner_add_right]

theorem convFun_smul (c : ℂ) (f : Lp ℂ 2 μ) : convFun μ ψ (c • f) = c • convFun μ ψ f := by
  ext x
  simp [convFun_def, inner_smul_right]

theorem convOp_ae (f : Lp ℂ 2 μ) : convOp μ ψ f =ᵐ[μ] convFun μ ψ f := by
  filter_upwards [L2Kernel.kernelOp_toLp_apply_ae (memLp_kerFun μ ψ) f] with x hx
  rw [convOp, hx, convFun_apply]
  rfl

theorem convFun_transl (h : C) (f : Lp ℂ 2 μ) (x : C) :
    convFun μ ψ (transl μ h f) x = convFun μ ψ f (h * x) := by
  rw [convFun_apply, convFun_apply]
  have e : ∫ y, (ψ (x / y) : ℂ) * (transl μ h f) y ∂μ = ∫ y, (ψ (x / y) : ℂ) * f (h * y) ∂μ :=
    integral_congr_ae (by
      filter_upwards [coeFn_transl μ h f] with y hy
      rw [hy])
  rw [e, ← integral_mul_left_eq_self (fun y => (ψ ((h * x) / y) : ℂ) * f y) h]
  simp only [mul_div_mul_left_eq_div]

theorem convOp_transl (h : C) (f : Lp ℂ 2 μ) :
    convOp μ ψ (transl μ h f) = transl μ h (convOp μ ψ f) := by
  refine Lp.ext ?_
  have e2 : (transl μ h (convOp μ ψ f) : C → ℂ) =ᵐ[μ] fun x => convFun μ ψ f (h * x) := by
    filter_upwards [coeFn_transl μ h (convOp μ ψ f),
      (measurePreserving_mul_left μ h).quasiMeasurePreserving.ae_eq_comp (convOp_ae μ ψ f)]
      with x h1 h2
    rw [h1]
    exact h2
  refine (convOp_ae μ ψ _).trans (e2.trans (Eventually.of_forall fun x => ?_)).symm
  exact (convFun_transl μ ψ h f x).symm

theorem integrable_of_L2 (f : Lp ℂ 2 μ) : Integrable f μ :=
  (Lp.memLp f).integrable one_le_two

theorem inner_convOp_left (f g : Lp ℂ 2 μ) :
    ⟪convOp μ ψ f, g⟫_ℂ = ∫ x, ∫ y, (ψ (x / y) : ℂ) * (conj (f y) * g x) ∂μ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [convOp_ae μ ψ f] with x hx
  rw [RCLike.inner_apply', hx, convFun_apply, ← integral_conj, ← integral_mul_const]
  congr 1
  funext y
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem inner_convOp_right (f g : Lp ℂ 2 μ) :
    ⟪f, convOp μ ψ g⟫_ℂ = ∫ y, ∫ x, (ψ (y / x) : ℂ) * (conj (f y) * g x) ∂μ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [convOp_ae μ ψ g] with y hy
  rw [RCLike.inner_apply', hy, convFun_apply, ← integral_const_mul]
  congr 1
  funext x
  ring

theorem isSelfAdjoint_convOp (hψ : ∀ z, ψ z⁻¹ = ψ z) : IsSelfAdjoint (convOp μ ψ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪convOp μ ψ f, g⟫_ℂ = ⟪f, convOp μ ψ g⟫_ℂ
  rw [inner_convOp_left, inner_convOp_right]
  have hint : Integrable (Function.uncurry fun x y => (ψ (x / y) : ℂ) * (conj (f y) * g x))
      (μ.prod μ) := by
    have hp : Integrable (fun z : C × C => g z.1 * conj (f z.2)) (μ.prod μ) :=
      (integrable_of_L2 μ g).mul_prod ((integrable_of_L2 μ f).norm.mono'
        (Complex.continuous_conj.comp_aestronglyMeasurable (integrable_of_L2 μ f).1)
        (Eventually.of_forall fun y => by simp))
    refine (hp.bdd_mul (continuous_kerFun ψ).aestronglyMeasurable
      (Eventually.of_forall (norm_kerFun_le ψ))).congr (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, kerFun]
    ring
  rw [integral_integral_swap hint]
  congr 1
  funext y
  congr 1
  funext x
  rw [← hψ (x / y), inv_div]

def diffForm (g : C) : Lp ℂ 2 μ →L[ℂ] ℂ := innerSL ℂ (row μ ψ 1 - row μ ψ g)

theorem diffForm_apply (g : C) (f : Lp ℂ 2 μ) :
    diffForm μ ψ g f = convFun μ ψ f 1 - convFun μ ψ f g := by
  simp [diffForm, convFun_def]

def symTransl : Bool × C → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
  | (true, h) => transl μ h + transl μ h⁻¹
  | (false, h) => Complex.I • (transl μ h - transl μ h⁻¹)

theorem inner_symTransl (i : Bool × C) (f g : Lp ℂ 2 μ) :
    ⟪symTransl μ i f, g⟫_ℂ = ⟪f, symTransl μ i g⟫_ℂ := by
  obtain ⟨b, h⟩ := i
  cases b
  · simp only [symTransl, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
      inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, inner_transl, inv_inv,
      Complex.conj_I]
    ring
  · simp only [symTransl, FunLike.coe_add, Pi.add_apply, inner_add_left, inner_add_right,
      inner_transl, inv_inv]
    ring

theorem commute_symTransl (i j : Bool × C) : Commute (symTransl μ i) (symTransl μ j) := by
  have c := commute_transl μ
  obtain ⟨b, h⟩ := i
  obtain ⟨b', h'⟩ := j
  cases b <;> cases b' <;> simp only [symTransl]
  · exact (((c _ _).sub_right (c _ _)).sub_left ((c _ _).sub_right (c _ _))).smul_left _ |>.smul_right _
  · exact (((c _ _).add_right (c _ _)).sub_left ((c _ _).add_right (c _ _))).smul_left _
  · exact (((c _ _).sub_right (c _ _)).add_left ((c _ _).sub_right (c _ _))).smul_right _
  · exact ((c _ _).add_right (c _ _)).add_left ((c _ _).add_right (c _ _))

theorem commute_convOp_symTransl (i : Bool × C) : Commute (convOp μ ψ) (symTransl μ i) := by
  have c : ∀ h, Commute (convOp μ ψ) (transl μ h) := fun h =>
    ContinuousLinearMap.ext fun f => by
      change convOp μ ψ (transl μ h f) = transl μ h (convOp μ ψ f)
      exact convOp_transl μ ψ h f
  obtain ⟨b, h⟩ := i
  cases b <;> simp only [symTransl]
  · exact ((c _).sub_right (c _)).smul_right _
  · exact (c _).add_right (c _)

include μ in

theorem exists_char_ne_one_alt {g : C} (hg : g ≠ 1) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  classical
  obtain ⟨W, hWo, hW1, hWW⟩ := exists_open_nhds_one_mul_subset
    (isOpen_compl_singleton.mem_nhds (Ne.symm hg) : ({g}ᶜ : Set C) ∈ 𝓝 1)
  obtain ⟨r, hr1, hr0, -, hr01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : C))) hWo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h hW1)
  let ψ : C(C, ℝ) := r * r.comp ⟨fun z => z⁻¹, continuous_inv⟩
  have hψ : ∀ z, ψ z = r z * r z⁻¹ := fun z => rfl
  have hψ_inv : ∀ z, ψ z⁻¹ = ψ z := fun z => by rw [hψ, hψ, inv_inv, mul_comm]
  have hr1' : r 1 = 1 := hr1 (Set.mem_singleton 1)
  have hψ1 : ψ 1 = 1 := by rw [hψ, inv_one, hr1', mul_one]
  have hψ0 : ∀ z ∉ W, ψ z = 0 := fun z hz => by rw [hψ, hr0 hz, Pi.zero_apply, zero_mul]
  have hT := isCompactOperator_convOp μ ψ
  have hT' := isSelfAdjoint_convOp μ ψ hψ_inv
  let ψc : C(C, ℂ) := ⟨fun z => (ψ z : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩
  let φ₂ : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ ψc
  have hconv : ∀ x, convFun μ ψ φ₂ x = ∫ y, ((ψ (x / y) * ψ y : ℝ) : ℂ) ∂μ := by
    intro x
    rw [convFun_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) ψc] with y hy
    rw [hy]
    simp [ψc]
  have hl1 : convFun μ ψ φ₂ 1 = ((∫ y, ψ y ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [hconv, integral_complex_ofReal]
    congr 2
    funext y
    rw [one_div, hψ_inv, sq]
  have hlg : convFun μ ψ φ₂ g = 0 := by
    have h0 : ∀ y, ψ (g / y) * ψ y = 0 := by
      intro y
      by_cases hy : y ∈ W
      · by_cases hgy : g / y ∈ W
        · exact absurd (div_mul_cancel g y) (hWW (Set.mul_mem_mul hgy hy))
        · rw [hψ0 _ hgy, zero_mul]
      · rw [hψ0 _ hy, mul_zero]
    rw [hconv]
    simp [h0]
  have hpos : 0 < ∫ y, ψ y ^ 2 ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (by fun_prop)
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
      (fun y => sq_nonneg _) (by simp [hψ1])
  have hℓφ : diffForm μ ψ g φ₂ ≠ 0 := by
    rw [diffForm_apply, hl1, hlg, sub_zero]
    exact_mod_cast hpos.ne'
  obtain ⟨s, b, l, hb, hTb, -, -⟩ :=
    CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hT'
  have hex : ∃ i, diffForm μ ψ g (b i) ≠ 0 := by
    by_contra hall
    have hall' : ∀ i, diffForm μ ψ g (b i) = 0 := fun i => by
      by_contra h
      exact hall ⟨i, h⟩
    have hs := (diffForm μ ψ g).hasSum (b.hasSum_repr φ₂)
    simp only [map_smul, hall', smul_zero] at hs
    exact hℓφ (hs.unique hasSum_zero)
  obtain ⟨i, hi⟩ := hex
  have hli : l i ≠ 0 := by
    intro h0
    apply hi
    have hz : convOp μ ψ (b i) = 0 := by rw [hTb, h0]; simp
    have hae : (convFun μ ψ (b i) : C → ℂ) =ᵐ[μ] (0 : C → ℂ) := by
      refine (convOp_ae μ ψ (b i)).symm.trans ?_
      rw [hz]
      exact Lp.coeFn_zero _ _ _
    have hcf := (Continuous.ae_eq_iff_eq μ (convFun μ ψ (b i)).continuous continuous_const).1 hae
    rw [diffForm_apply, congrFun hcf 1, congrFun hcf g]
    simp
  set T := convOp μ ψ with hTdef
  set E := eigenspace T.toLinearMap (l i : ℂ) with hEdef
  have : FiniteDimensional ℂ E := ContinuousLinearMap.finite_dimensional_eigenspace hT _ (Complex.ofReal_ne_zero.2 hli)
  have hbE : b i ∈ E := mem_eigenspace_iff.2 (hTb i)
  have hmaps : ∀ j, Set.MapsTo (symTransl μ j) E E := by
    intro j f hf
    rw [SetLike.mem_coe, mem_eigenspace_iff] at hf ⊢
    change T (symTransl μ j f) = _
    have hc := congrArg (fun A => A f) (commute_convOp_symTransl μ ψ j).eq
    simp only [mul_apply_eq_comp] at hc
    rw [hc]
    change symTransl μ j (T f) = _
    rw [show T f = (l i : ℂ) • f from hf, map_smul]
  let Op : Bool × C → Module.End ℂ E := fun j =>
    (symTransl μ j : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).restrict (hmaps j)
  have hOp : ∀ j (x : E), ((Op j x : E) : Lp ℂ 2 μ) = symTransl μ j x := fun j x => rfl
  have hsym : ∀ j, (Op j).IsSymmetric := fun j x y => by
    rw [Submodule.coe_inner, Submodule.coe_inner, hOp, hOp]
    exact inner_symTransl μ j x y
  have hcomm : Pairwise (Function.onFun Commute Op) := by
    intro j k _
    change Op j * Op k = Op k * Op j
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hOp, hOp, hOp, hOp]
    have hc := congrArg (fun A => A (x : Lp ℂ 2 μ)) (commute_symTransl μ j k).eq
    simpa only [mul_apply_eq_comp] using hc
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  let ℓE : E →ₗ[ℂ] ℂ := (diffForm μ ψ g : Lp ℂ 2 μ →ₗ[ℂ] ℂ).comp E.subtype
  obtain ⟨γ, w, hw, hℓw⟩ : ∃ γ : Bool × C → ℂ, ∃ w ∈ ⨅ j, eigenspace (Op j) (γ j), ℓE w ≠ 0 := by
    by_contra hno
    have hle : (⨆ γ : Bool × C → ℂ, ⨅ j, eigenspace (Op j) (γ j)) ≤ LinearMap.ker ℓE :=
      iSup_le fun γ w hw => LinearMap.mem_ker.2 (by
        by_contra h
        exact hno ⟨γ, w, hw, h⟩)
    rw [htop] at hle
    exact hi (LinearMap.mem_ker.1 (hle (Submodule.mem_top (x := (⟨b i, hbE⟩ : E)))))
  have heig : ∀ j, symTransl μ j (w : Lp ℂ 2 μ) = γ j • (w : Lp ℂ 2 μ) := by
    intro j
    have h := (Submodule.mem_iInf _).1 hw j
    rw [mem_eigenspace_iff] at h
    rw [← hOp, h]
    rfl
  have htr : ∀ h : C, ∃ c : ℂ, transl μ h w = c • (w : Lp ℂ 2 μ) := by
    intro h
    refine ⟨(γ (true, h) - Complex.I * γ (false, h)) / 2, ?_⟩
    have e1 := heig (true, h)
    have e2 := heig (false, h)
    simp only [symTransl, _root_.add_apply, _root_.smul_apply, _root_.sub_apply] at e1 e2
    set u := transl μ h (w : Lp ℂ 2 μ)
    set v := transl μ h⁻¹ (w : Lp ℂ 2 μ)
    have e3 : u - v = (-(Complex.I * γ (false, h))) • (w : Lp ℂ 2 μ) := by
      have h3 := congrArg (fun z => (-Complex.I) • z) e2
      simp only [smul_smul] at h3
      rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
        at h3
      rw [h3]
      congr 1
      ring
    calc u = (1 / 2 : ℂ) • ((u + v) + (u - v)) := by module
      _ = (1 / 2 : ℂ) • (γ (true, h) • (w : Lp ℂ 2 μ) + (-(Complex.I * γ (false, h))) • (w : Lp ℂ 2 μ)) := by
        rw [e1, e3]
      _ = ((γ (true, h) - Complex.I * γ (false, h)) / 2) • (w : Lp ℂ 2 μ) := by module
  have hF : ∀ h : C, ∃ c : ℂ, ∀ x, convFun μ ψ w (h * x) = c * convFun μ ψ w x := by
    intro h
    obtain ⟨c, hc⟩ := htr h
    exact ⟨c, fun x => by rw [← convFun_transl, hc, convFun_smul]; rfl⟩
  have hF1g : convFun μ ψ w 1 ≠ convFun μ ψ w g := fun h => hℓw (by
    change diffForm μ ψ g (w : Lp ℂ 2 μ) = 0
    rw [diffForm_apply, h, sub_self])
  exact exists_char_of_translate (convFun μ ψ w).continuous hF1g hF

end Metrizable

theorem exists_char_ne_one_of_secondCountable [SecondCountableTopology C] {g : C} (hg : g ≠ 1) :
    ∃ χ : C →ₜ* Circle, χ g ≠ 1 := by
  borelize C
  exact exists_char_ne_one_alt (μ := Measure.haar) hg

theorem exists_char_ne_one {g : C} (hg : g ≠ 1) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 :=
  _root_.UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one hg

theorem exists_char_ne {x y : C} (hxy : x ≠ y) : ∃ χ : C →ₜ* Circle, χ x ≠ χ y := by
  obtain ⟨χ, hχ⟩ := exists_char_ne_one (g := x * y⁻¹) (fun h => hxy (mul_inv_eq_one.1 h))
  refine ⟨χ, fun h => hχ ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

def charCM (χ : C →ₜ* Circle) : C(C, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩

theorem charCM_apply (χ : C →ₜ* Circle) (x : C) : charCM χ x = (χ x : ℂ) := rfl

theorem charCM_mul (χ χ' : C →ₜ* Circle) : charCM (χ * χ') = charCM χ * charCM χ' := by
  ext x
  simp [charCM_apply]

theorem charCM_one : charCM (1 : C →ₜ* Circle) = 1 := by
  ext x
  simp [charCM_apply]

theorem star_charCM (χ : C →ₜ* Circle) : star (charCM χ) = charCM χ⁻¹ := by
  ext x
  change conj ((χ x : Circle) : ℂ) = (((χ x)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]

def charAlgebra : StarSubalgebra ℂ C(C, ℂ) :=
  { (Submodule.span ℂ (Set.range (charCM (C := C)))).toSubalgebra
      (Submodule.subset_span ⟨1, charCM_one⟩)
      (fun a b ha hb => by
        induction ha using Submodule.span_induction with
        | mem x hx =>
          induction hb using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨χ, rfl⟩ := hx
            obtain ⟨χ', rfl⟩ := hy
            exact Submodule.subset_span ⟨χ * χ', charCM_mul χ χ'⟩
          | zero => rw [mul_zero]; exact Submodule.zero_mem _
          | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
          | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) with
    star_mem' := fun {a} ha => by
      change a ∈ Submodule.span ℂ (Set.range (charCM (C := C))) at ha
      change star a ∈ Submodule.span ℂ (Set.range (charCM (C := C)))
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        exact Submodule.subset_span ⟨χ⁻¹, (star_charCM χ).symm⟩
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

theorem mem_charAlgebra {f : C(C, ℂ)} :
    f ∈ charAlgebra (C := C) ↔ f ∈ Submodule.span ℂ (Set.range (charCM (C := C))) := Iff.rfl

theorem charAlgebra_separatesPoints : (charAlgebra (C := C)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨χ, hχ⟩ := exists_char_ne hxy
  exact ⟨charCM χ, ⟨charCM χ, Submodule.subset_span ⟨χ, rfl⟩, rfl⟩, fun h => hχ (Circle.coe_injective h)⟩

theorem span_charCM_dense :
    (Submodule.span ℂ (Set.range (charCM (C := C)))).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (charAlgebra_separatesPoints (C := C))
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (charAlgebra (C := C)).topologicalClosure := by rw [h]; trivial
  exact hf

theorem conj_mul_self_circle (z : Circle) : conj (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

section L2

variable [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]

def charL2 (χ : C →ₜ* Circle) : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ (charCM χ)

theorem coeFn_charL2 (χ : C →ₜ* Circle) : charL2 μ χ =ᵐ[μ] fun x => (χ x : ℂ) :=
  ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (charCM χ)

theorem inner_charL2 (χ χ' : C →ₜ* Circle) :
    ⟪charL2 μ χ, charL2 μ χ'⟫_ℂ = ∫ x, conj (χ x : ℂ) * χ' x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_charL2 μ χ, coeFn_charL2 μ χ'] with x h1 h2
  rw [RCLike.inner_apply', h1, h2]

theorem integral_conj_mul_eq_zero {χ χ' : C →ₜ* Circle} (h : χ ≠ χ') :
    ∫ x, conj (χ x : ℂ) * χ' x ∂μ = 0 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
  set c : ℂ := conj (χ a : ℂ) * χ' a
  have key : ∫ x, conj (χ x : ℂ) * χ' x ∂μ = c * ∫ x, conj (χ x : ℂ) * χ' x ∂μ := by
    calc ∫ x, conj (χ x : ℂ) * χ' x ∂μ = ∫ x, conj (χ (a * x) : ℂ) * χ' (a * x) ∂μ :=
          (integral_mul_left_eq_self (fun x => conj (χ x : ℂ) * χ' x) a).symm
      _ = ∫ x, c * (conj (χ x : ℂ) * χ' x) ∂μ := by
          congr 1
          funext x
          simp only [c, map_mul, Circle.coe_mul]
          ring
      _ = c * ∫ x, conj (χ x : ℂ) * χ' x ∂μ := integral_const_mul _ _
  have hc : c ≠ 1 := by
    intro h1
    apply ha
    refine Circle.coe_injective ?_
    calc (χ a : ℂ) = (χ a : ℂ) * c := by rw [h1, mul_one]
      _ = χ' a := by
        simp only [c]
        rw [← mul_assoc, mul_comm (χ a : ℂ), conj_mul_self_circle, one_mul]
  have h0 : (1 - c) * ∫ x, conj (χ x : ℂ) * χ' x ∂μ = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hc))

variable [IsProbabilityMeasure μ]

theorem orthonormal_charL2 : Orthonormal ℂ (charL2 (C := C) μ) := by
  classical
  rw [orthonormal_iff_ite]
  intro χ χ'
  rw [inner_charL2]
  split_ifs with h
  · subst h
    simp [conj_mul_self_circle]
  · exact integral_conj_mul_eq_zero μ h

theorem span_charL2_dense :
    ⊤ ≤ (Submodule.span ℂ (Set.range (charL2 (C := C) μ))).topologicalClosure := by
  intro f _
  have hd := ContinuousMap.toLp_denseRange ℂ μ ℂ (p := 2) ENNReal.ofNat_ne_top
  have hmaps : Set.MapsTo (ContinuousMap.toLp 2 μ ℂ : C(C, ℂ) →L[ℂ] Lp ℂ 2 μ)
      (Submodule.span ℂ (Set.range (charCM (C := C))))
      (Submodule.span ℂ (Set.range (charL2 (C := C) μ))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨χ, rfl⟩ := hy
      exact Submodule.subset_span ⟨χ, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  have h1 : Set.range (ContinuousMap.toLp 2 μ ℂ : C(C, ℂ) →L[ℂ] Lp ℂ 2 μ) ⊆
      ((Submodule.span ℂ (Set.range (charL2 (C := C) μ))).topologicalClosure : Set (Lp ℂ 2 μ)) := by
    rintro _ ⟨g, rfl⟩
    have hg : g ∈ closure (Submodule.span ℂ (Set.range (charCM (C := C))) : Set C(C, ℂ)) := by
      rw [← Submodule.topologicalClosure_coe, span_charCM_dense]
      trivial
    rw [Submodule.topologicalClosure_coe]
    exact map_mem_closure (ContinuousMap.toLp 2 μ ℂ).continuous hg hmaps
  exact closure_minimal h1 (Submodule.isClosed_topologicalClosure _) (hd f)

def charBasis : HilbertBasis (C →ₜ* Circle) ℂ (Lp ℂ 2 μ) :=
  HilbertBasis.mk (orthonormal_charL2 μ) (span_charL2_dense μ)

theorem coe_charBasis : ⇑(charBasis (C := C) μ) = charL2 μ :=
  HilbertBasis.coe_mk _ _

theorem hasSum_fourier (f : Lp ℂ 2 μ) :
    HasSum (fun χ : C →ₜ* Circle => ⟪charL2 μ χ, f⟫_ℂ • charL2 μ χ) f := by
  have h := (charBasis μ).hasSum_repr f
  simpa only [HilbertBasis.repr_apply_apply, coe_charBasis] using h

theorem hasSum_norm_sq_fourier (f : Lp ℂ 2 μ) :
    HasSum (fun χ : C →ₜ* Circle => ‖⟪charL2 μ χ, f⟫_ℂ‖ ^ 2) (‖f‖ ^ 2) := by
  have h := (charBasis μ).hasSum_inner_mul_inner f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [coe_charBasis] at h
  have e : ∀ χ, ⟪f, charL2 μ χ⟫_ℂ * ⟪charL2 μ χ, f⟫_ℂ = ((‖⟪charL2 μ χ, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) :=
    fun χ => by rw [← inner_conj_symm, Complex.conj_mul']; push_cast; ring
  have h2 : HasSum (fun χ => ((‖⟪charL2 μ χ, f⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    simp only [e] at h
    rw [Complex.ofReal_pow]
    exact h
  exact Complex.hasSum_ofReal.1 h2

theorem inner_charL2_toLp (χ : C →ₜ* Circle) (f : C(C, ℂ)) :
    ⟪charL2 μ χ, ContinuousMap.toLp 2 μ ℂ f⟫_ℂ = ∫ x, conj (χ x : ℂ) * f x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_charL2 μ χ,
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) f] with x h1 h2
  rw [RCLike.inner_apply', h1, h2]

end L2

end

end GroundTheory.Automorphic.CompactAbelianFourier
