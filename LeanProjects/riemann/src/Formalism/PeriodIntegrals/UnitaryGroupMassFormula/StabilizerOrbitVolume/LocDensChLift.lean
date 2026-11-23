import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAChar

noncomputable section

open NumberField Complex

namespace PI.VolStabSW

namespace ChLiftW

theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  by_contra hne
  rw [hn] at hne
  have hn0 : n ≠ 0 := by exact_mod_cast hne
  rcases lt_or_gt_of_ne hn0 with hlt | hgt
  · have hiv := isPreconnected_univ.intermediate_value (Set.mem_univ p) (Set.mem_univ a) hψ.continuousOn
    have hle : (n : ℝ) ≤ -1 := by
      have h' : n ≤ -1 := by omega
      exact_mod_cast h'
    have hm : (-1 / 2 : ℝ) ∈ Set.Icc (ψ p) (ψ a) := by
      rw [hn, ha]; constructor <;> linarith
    obtain ⟨q, -, hq⟩ := hiv hm
    obtain ⟨m, hm'⟩ := hint q
    rw [hm'] at hq
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hiv := isPreconnected_univ.intermediate_value (Set.mem_univ a) (Set.mem_univ p) hψ.continuousOn
    have hle : (1 : ℝ) ≤ n := by
      have h' : 1 ≤ n := by omega
      exact_mod_cast h'
    have hm : (1 / 2 : ℝ) ∈ Set.Icc (ψ a) (ψ p) := by
      rw [hn, ha]; constructor <;> linarith
    obtain ⟨q, -, hq⟩ := hiv hm
    obtain ⟨m, hm'⟩ := hint q
    rw [hm'] at hq
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := by
    intro x h
    have h1 := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at h1
    exact one_ne_zero h1
  have hpow : ∀ (k : ℕ) (y : W), χ ((k : ℝ) • y) = χ y ^ k := by
    intro k y
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y : W, ‖y‖ ≤ δ → ‖χ y - 1‖ < 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    have h2 := h (x := y) (by rw [dist_zero_right]; linarith)
    rwa [h0, dist_eq_norm] at h2
  have hre : ∀ y : W, ‖y‖ ≤ δ → 0 < (χ y).re := by
    intro y hy
    have h1 := hball y hy
    have h2 : |(χ y - 1).re| ≤ ‖χ y - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.1 (h2.trans h1.le)).1
    linarith
  have harg : ∀ y : W, ‖y‖ ≤ δ → |Complex.arg (χ y)| < Real.pi / 2 := fun y hy =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre y hy))
  set L : W → ℂ := fun y => Complex.log (χ y) with hL
  have hL0 : L 0 = 0 := by simp [hL, h0]
  have hLadd : ∀ y z : W, ‖y‖ ≤ δ → ‖z‖ ≤ δ → L (y + z) = L y + L z := by
    intro y z hy hz
    simp only [hL]
    have h1 := abs_lt.1 (harg y hy)
    have h2 := abs_lt.1 (harg z hz)
    rw [hadd, Complex.log_mul (hne y) (hne z)]
    constructor <;> linarith [Real.pi_pos]
  have hLsmul : ∀ (k : ℕ) (y : W), (k : ℝ) * ‖y‖ ≤ δ → L ((k : ℝ) • y) = k * L y := by
    intro k y
    induction k with
    | zero => intro _; simp [hL0]
    | succ k ih =>
      intro hk
      have hy0 := norm_nonneg y
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hk
      have h1 : (k : ℝ) * ‖y‖ ≤ δ := by nlinarith
      have h2 : ‖y‖ ≤ δ := by nlinarith
      have h3 : ‖(k : ℝ) • y‖ ≤ δ := by rw [norm_smul, Real.norm_natCast]; exact h1
      rw [Nat.cast_succ, add_smul, one_smul, hLadd _ _ h3 h2, ih h1]
      push_cast
      ring
  have hkey : ∀ (a b : ℕ) (x : W), 0 < a → 0 < b → ‖x‖ ≤ a * δ → ‖x‖ ≤ b * δ →
      (a : ℂ) * L ((a : ℝ)⁻¹ • x) = (b : ℂ) * L ((b : ℝ)⁻¹ • x) := by
    intro a b x ha hb hxa hxb
    have ha' : (0 : ℝ) < a := Nat.cast_pos.2 ha
    have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
    have e1 : (b : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (a : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have e2 : (a : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (b : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have ny : ‖((a : ℝ) * b)⁻¹ • x‖ = ‖x‖ / (a * b) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
      ring
    have hb1 : (b : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (b : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / a by field_simp, div_le_iff₀ ha']
      linarith
    have ha1 : (a : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (a : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / b by field_simp, div_le_iff₀ hb']
      linarith
    rw [← e1, ← e2, hLsmul b _ hb1, hLsmul a _ ha1]
    ring
  set N : W → ℕ := fun x => ⌈‖x‖ / δ⌉₊ + 1 with hN
  have hNpos : ∀ x, 0 < N x := fun x => Nat.succ_pos _
  have hNle : ∀ x, ‖x‖ ≤ (N x : ℝ) * δ := by
    intro x
    have h1 : ‖x‖ / δ ≤ ⌈‖x‖ / δ⌉₊ := Nat.le_ceil _
    have h2 : ‖x‖ ≤ (⌈‖x‖ / δ⌉₊ : ℝ) * δ := by rwa [div_le_iff₀ hδ] at h1
    simp only [hN]
    push_cast
    nlinarith
  set f : W → ℂ := fun x => (N x : ℂ) * L ((N x : ℝ)⁻¹ • x) with hf
  have hfM : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → f x = M * L ((M : ℝ)⁻¹ • x) :=
    fun M x hM hx => hkey (N x) M x (hNpos x) hM (hNle x) hx
  have hsmall : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → ‖(M : ℝ)⁻¹ • x‖ ≤ δ := by
    intro M x hM hx
    have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hM'.le, inv_mul_le_iff₀ hM']
    linarith
  have fadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have hMpos : 0 < N x + N y := by have := hNpos x; omega
    have hcx : (N x : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N x ≤ N x + N y)
    have hcy : (N y : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N y ≤ N x + N y)
    have hx : ‖x‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle x).trans hcx
    have hy : ‖y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle y).trans hcy
    have hxy : ‖x + y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      have h1 := norm_add_le x y
      have h2 := hNle x
      have h3 := hNle y
      push_cast
      linarith
    rw [hfM _ (x + y) hMpos hxy, hfM _ x hMpos hx, hfM _ y hMpos hy, smul_add,
      hLadd _ _ (hsmall _ x hMpos hx) (hsmall _ y hMpos hy), mul_add]
  have fexp : ∀ x, χ x = Complex.exp (f x) := by
    intro x
    show χ x = Complex.exp ((N x : ℂ) * Complex.log (χ ((N x : ℝ)⁻¹ • x)))
    rw [Complex.exp_nat_mul, Complex.exp_log (hne _), ← hpow, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast (hNpos x).ne'), one_smul]
  have fcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hMpos : 0 < N x0 + 1 := Nat.succ_pos _
    have hMr : ((N x0 + 1 : ℕ) : ℝ) = N x0 + 1 := by push_cast; ring
    have hx0 : ‖x0‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
      rw [hMr]
      nlinarith [hNle x0]
    have heq : (fun x => ((N x0 + 1 : ℕ) : ℂ) * L (((N x0 + 1 : ℕ) : ℝ)⁻¹ • x)) =ᶠ[nhds x0] f := by
      filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h1 : ‖x‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
        have h2 := norm_sub_norm_le x x0
        rw [hMr]
        nlinarith [hNle x0]
      exact (hfM _ x hMpos h1).symm
    refine ContinuousAt.congr ?_ heq
    apply ContinuousAt.mul continuousAt_const
    simp only [hL]
    apply ContinuousAt.clog
    · exact (hc.comp (continuous_const_smul _)).continuousAt
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (hre _ (hsmall _ x0 hMpos hx0)))
  exact ⟨AddMonoidHom.mk' f fadd, fcont, fexp⟩

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have he0 : e 0 = 0 := by simpa using he 0 0
  have hs0 : e.symm 0 = 0 := by rw [← he0, Homeomorph.symm_apply_apply]
  have hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous)
    (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])
  refine ⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add]),
    hℓc.comp e.continuous, fun x => ?_⟩
  have h1 := hℓ (e x)
  simp only [Homeomorph.symm_apply_apply] at h1
  exact h1

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y) χ hc hadd h0
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  refine Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW

open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by
  simp only [sgl]
  exact Finset.univ_sum_single x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have key : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := by
    intro v
    exact lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓ hℓc hℓ using key
  refine ⟨AddMonoidHom.mk' (fun x => ∑ v, ℓ v (x v)) (fun x y => ?_), ?_, fun x => ?_⟩
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_add]
    rfl
  · exact continuous_finset_sum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · show χ x = Complex.exp (∑ v, ℓ v (x v))
    conv_lhs => rw [← sum_sgl x]
    rw [ChLiftW.addChar_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabSW
