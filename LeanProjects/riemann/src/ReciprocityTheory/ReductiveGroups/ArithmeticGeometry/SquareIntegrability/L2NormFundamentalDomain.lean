import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCauchy

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

theorem contDiff_of_diff {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {f : W → ℂ} (hf : Differentiable ℂ f) : ContDiff ℂ (⊤ : ℕ∞) f := by
  let e := (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (f ∘ e.symm) := by
    first
    | exact hf.comp e.symm.differentiable
    | exact hf.comp (e.symm.contDiff.differentiable (by simp))
  have h3 := (contDiff_of_differentiable h1 (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp e.contDiff
  convert h3 using 1
  funext v; simp

theorem jof_Hf_self_re {ι : Type} [Fintype ι] (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq x, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Hf, Complex.re_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
  | rw [← Complex.ofReal_pow, Complex.ofReal_re]
  | norm_cast
  | simp [sq]

variable {E : Type} [Field E] [NumberField E] (X : PT E)

def tens {n : ℕ} (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) : (Fin n → Vsp X.dim) → ℂ :=
  fun v => ∏ k, s k (fun _ => v k)

theorem col_contDiff {q : ℕ} {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1) :
    ContDiff ℂ (⊤ : ℕ∞) (fun z : Vsp X.dim => s (fun _ => z)) := by
  have hd : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  apply contDiff_of_diff
  first
  | exact hd.comp (differentiable_pi.mpr fun _ => differentiable_id)
  | fun_prop

theorem sec_contDiff {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  exact contDiff_of_diff (show Differentiable ℂ F ∧ _ from hF).1

theorem tens_mem {n q : ℕ} {s : Fin n → (Fin 1 → Vsp X.dim) → ℂ} (hs : ∀ k, s k ∈ X.Sec q 1) :
    tens X s ∈ X.Sec q n := by
  have hd : ∀ k, Differentiable ℂ (s k) := fun k => (show Differentiable ℂ (s k) ∧ _ from hs k).1
  show _ ∧ _
  refine ⟨?_, fun γ hγ v => ?_⟩
  · show Differentiable ℂ (fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k))
    first
    | exact Differentiable.finset_prod (fun k _ => (hd k).comp (differentiable_pi.mpr fun _ => differentiable_apply k))
    | fun_prop
  · have he : ∀ k, s k (fun _ => (v + γ) k) = ((X.eps (γ k) : ℂ)) ^ q *
        cexp (q * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) * s k (fun _ => v k) := by
      intro k
      have := (show Differentiable ℂ (s k) ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s k (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s k w from hs k).2
        (fun _ => γ k) (fun _ => hγ k) (fun _ => v k)
      simpa [HC, Pi.add_def] using this
    have hsum : ∑ k, ((q : ℂ) * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) =
        q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 := by
      simp only [HC, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    show ∏ k, s k (fun _ => (v + γ) k) = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
      cexp (q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) * ∏ k, s k (fun _ => v k)
    rw [Finset.prod_congr rfl fun k _ => he k, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow, ← Complex.exp_sum, hsum]

theorem pointNormSq_tensor {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    X.ptN2 q (tens X s) v = ∏ k, X.ptN2 q (s k) (fun _ => v k) := by
  have hHC : (HC v v).re = ∑ k, (HC (fun _ : Fin 1 => v k) (fun _ => v k)).re := by
    simp [HC, Complex.re_sum]
  simp only [PT.ptN2, tens]
  rw [norm_prod, ← Finset.prod_pow, hHC, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]

theorem avg_fd_prod {n : ℕ} (f : Fin n → Vsp X.dim → ℝ) :
    ⨍ v in X.fd n, ∏ k, f k (v k) = ∏ k, ⨍ x in ZSpan.fundamentalDomain X.b, f k x := by
  have hfd : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
    ext v; simp [PT.fd]
  rw [hfd]
  simp only [MeasureTheory.setAverage_eq, smul_eq_mul]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  simp only [MeasureTheory.measureReal_def]
  rw [MeasureTheory.Measure.pi_pi, ENNReal.toReal_prod, ← Finset.prod_inv_distrib]
  first
  | rw [MeasureTheory.integral_fintype_prod_eq_prod, ← Finset.prod_mul_distrib]
  | rw [MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => _), ← Finset.prod_mul_distrib]

theorem l2_norm_fundamental_domain (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q s = ⨍ x in ZSpan.fundamentalDomain X.b, X.ptN2 q s (fun _ => x) := by
  have hv : ∀ v : Fin 1 → Vsp X.dim, (fun _ : Fin 1 => v 0) = v :=
    fun v => funext fun k => by rw [Subsingleton.elim k 0]
  have h := avg_fd_prod X (n := 1) (fun _ x => X.ptN2 q s (fun _ => x))
  simp only [Fin.prod_univ_one, hv] at h
  exact h

theorem l2_tens_eq_prod {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q (tens X s) = ∏ k, X.l2 q (s k) := by
  rw [Finset.prod_congr rfl fun k _ => l2_norm_fundamental_domain X q (s k)]
  rw [PT.l2]
  simp_rw [pointNormSq_tensor X q s]
  exact avg_fd_prod X (fun k x => X.ptN2 q (s k) (fun _ => x))

theorem l2_smul {n : ℕ} (q : ℕ) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.l2 q (c • F) = ‖c‖ ^ 2 * X.l2 q F := by
  have h : ∀ v, X.ptN2 q (c • F) v = ‖c‖ ^ 2 * X.ptN2 q F v := by
    intro v
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  simp only [PT.l2, h]
  first
  | exact MeasureTheory.integral_const_mul _ _
  | exact MeasureTheory.integral_mul_left _ _
  | simp [MeasureTheory.average, MeasureTheory.integral_const_mul]

def gtOf (q : ℕ) : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun γ => (X.eps γ : ℂ) ^ q
  ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h]

theorem eq_zero_of_l2_eq_zero (hP : Ext.PackingCount) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec q 1) (h0 : X.l2 q s = 0) : s = 0 := by
  have hd : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  set g : Vsp X.dim → ℂ := fun z => s (fun _ => z) with hgdef
  have hgc : Continuous g := (hd.comp (differentiable_pi.mpr fun _ => differentiable_id)).continuous
  have hq' : ∀ γ ∈ X.L, ∀ x, g (x + γ) = ((X.eps γ : ℂ)) ^ q *
      cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * g x := by
    intro γ hγ x
    have := (show Differentiable ℂ s ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s w from hs).2
      (fun _ => γ) (fun _ => hγ) (fun _ => x)
    simpa [HC, Pi.add_def, hgdef] using this
  have hne : ∀ γ ∈ X.L, ∀ x, g (x + γ) = 0 ↔ g x = 0 := by
    intro γ hγ x
    rw [hq' γ hγ x]
    have h1 : (X.eps γ : ℂ) ≠ 0 := by rcases X.eps_pm γ hγ with h | h <;> simp [h]
    simp [h1, Complex.exp_ne_zero]
  have hpx : ∀ x, X.ptN2 q s (fun _ => x) = ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    intro x
    have hre : (HC (fun _ : Fin 1 => x) (fun _ => x)).re = ‖x‖ ^ 2 := by simp [HC, jof_Hf_self_re]
    simp only [PT.ptN2, hre, hgdef]
  have hl := l2_norm_fundamental_domain X q s
  rw [h0] at hl
  simp only [hpx] at hl
  set D := ZSpan.fundamentalDomain X.b with hD
  have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet X.b
  have hDb : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded X.b
  haveI : MeasureTheory.VAddInvariantMeasure (Submodule.span ℤ (Set.range X.b)) (Vsp X.dim)
      MeasureTheory.volume :=
    ⟨fun c s _ => by
      simpa [Submodule.vadd_def, vadd_eq_add] using
        MeasureTheory.measure_preimage_add MeasureTheory.volume (c : Vsp X.dim) s⟩
  have hfd := ZSpan.isAddFundamentalDomain X.b (MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim))
  have hD0 : MeasureTheory.volume D ≠ 0 := hfd.measure_ne_zero (NeZero.ne _)
  have hDt : MeasureTheory.volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hcont : Continuous fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    first
    | fun_prop
    | exact ((continuous_norm.comp hgc).pow 2).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hint : MeasureTheory.IntegrableOn
      (fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2)) D :=
    (hcont.continuousOn.integrableOn_compact hDb.isCompact_closure).mono_set subset_closure
  rw [MeasureTheory.setAverage_eq, smul_eq_mul] at hl
  have hI : ∫ x in D, ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) = 0 := by
    have hr : MeasureTheory.volume.real D ≠ 0 := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_ne_zero.mpr ⟨hD0, hDt⟩
    rcases mul_eq_zero.mp hl.symm with h | h
    · exact absurd (inv_eq_zero.mp h) hr
    · exact h
  have hae := (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
    (MeasureTheory.ae_of_all _ fun x => by show (0:ℝ) ≤ _; positivity) hint).mp hI
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim)), x ∈ D → g x = 0 := by
    rw [← MeasureTheory.ae_restrict_iff' hDm]
    filter_upwards [hae] with x hx
    simpa [Real.exp_ne_zero] using hx
  rw [MeasureTheory.ae_iff] at h2
  have hset : {x | ¬(x ∈ D → g x = 0)} = {x | g x ≠ 0} ∩ D := by
    ext x; simp [and_comm]
  rw [hset] at h2
  open Pointwise in
  have hinv : ∀ γ : Submodule.span ℤ (Set.range X.b), γ +ᵥ {x | g x ≠ 0} = {x | g x ≠ 0} := by
    intro γ
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [Set.mem_setOf_eq]
    have e : (-γ) +ᵥ y = y + -(γ : Vsp X.dim) := by
      first
      | (rw [Submodule.vadd_def, add_comm]; rfl)
      | simp [Submodule.vadd_def, add_comm]
      | (show ((-γ : Submodule.span ℤ (Set.range X.b)) : Vsp X.dim) + y = _; simp [add_comm])
    rw [e]
    exact not_congr (hne _ (neg_mem γ.2) y)
  have ht0 := hfd.measure_zero_of_invariant {x | g x ≠ 0} hinv h2
  have hopen : IsOpen {x | g x ≠ 0} := isOpen_ne_fun hgc continuous_const
  have hempty : {x | g x ≠ 0} = ∅ := (hopen.measure_eq_zero_iff MeasureTheory.volume).mp ht0
  funext v
  show s v = 0
  have hv : v = fun _ => v 0 := funext fun k => by rw [Subsingleton.elim k 0]
  have hz : g (v 0) = 0 := by
    by_contra hc
    have hm : v 0 ∈ ({x | g x ≠ 0} : Set (Vsp X.dim)) := hc
    rw [hempty] at hm
    exact hm
  rw [hv]
  exact hz

theorem polyDeriv_zero_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) : polyDeriv P u (0 : W → ℂ) x = 0 := by
  simp [polyDeriv, Pi.zero_def]

theorem polyDeriv_smul_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  first
  | rw [iteratedFDeriv_const_smul_apply ((hF.of_le (by exact_mod_cast le_top)).contDiffAt)]
  | rw [iteratedFDeriv_const_smul_apply (hF.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

end

end ReciprocityTheory.ChartRestriction.G.I2
