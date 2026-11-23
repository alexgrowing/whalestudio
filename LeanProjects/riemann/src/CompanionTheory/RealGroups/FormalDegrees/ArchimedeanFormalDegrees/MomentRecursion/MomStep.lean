import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.MomB

open MeasureTheory Set

namespace CompanionTheory.RgFd

theorem mom_step {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω} {ν' : Measure Ω'} {V : Ω → ℝ}
    {V' : Ω' → ℝ} (hV : Measurable V) (hV' : Measurable V') (h0 : ∀ x, 0 ≤ V x ∧ V x ≤ 1) (h0' : ∀ y, 0 ≤ V' y ∧ V' y ≤ 1)
    (he : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j) ∂ν')
    (hf : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν ≠ ⊤) (M : ℕ) : ∀ j : ℕ, 1 ≤ j →
    ∫⁻ x, ENNReal.ofReal (V x ^ j * (1 - V x) ^ M) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j * (1 - V' y) ^ M) ∂ν' := by
  have split : ∀ {A : Type} [MeasurableSpace A] (m : Measure A) (W : A → ℝ), Measurable W → (∀ x, 0 ≤ W x ∧ W x ≤ 1) →
      ∀ j M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ j * (1 - W x) ^ M) ∂m =
        ∫⁻ x, ENNReal.ofReal (W x ^ j * (1 - W x) ^ (M + 1)) ∂m + ∫⁻ x, ENNReal.ofReal (W x ^ (j + 1) * (1 - W x) ^ M) ∂m := by
    intro A _ m W hW h j M
    rw [← lintegral_add_left (by fun_prop)]
    refine lintegral_congr fun x => ?_
    have a := (h x).1
    have b := sub_nonneg.2 (h x).2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  induction M with
  | zero => simpa using he
  | succ M ih =>
    intro j hj
    have fin : ∫⁻ x, ENNReal.ofReal (V x ^ (j + 1) * (1 - V x) ^ M) ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hf (j + 1) (by omega)) (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
      have a := (h0 x).1
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (sub_nonneg.2 (h0 x).2) (by linarith))
    have e := ih j hj
    rw [split ν V hV h0 j M, split ν' V' hV' h0' j M, ← ih (j + 1) (by omega)] at e
    exact (ENNReal.add_left_inj fin).1 e

theorem mom_sum {A : Type} [MeasurableSpace A] (m : Measure A) {W : A → ℝ} (hW : Measurable W) (h : ∀ x, 0 ≤ W x ∧ W x ≤ 1) :
    m {x | 0 < W x} = ∑' M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M) ∂m := by
  rw [← lintegral_tsum fun M => (by fun_prop : Measurable fun x => ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M)).aemeasurable,
    ← lintegral_indicator_one (measurableSet_lt measurable_const hW)]
  refine lintegral_congr fun x => ?_
  have a := (h x).1
  have b := sub_nonneg.2 (h x).2
  by_cases hx : 0 < W x
  · have hs : HasSum (fun M : ℕ => W x ^ 1 * (1 - W x) ^ M) (W x ^ 1 * (1 - (1 - W x))⁻¹) :=
      (hasSum_geometric_of_lt_one b (by linarith)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun M => by positivity) hs.summable, hs.tsum_eq,
      indicator_of_mem (show x ∈ {x | 0 < W x} from hx)]
    simp [mul_inv_cancel₀ hx.ne']
  · rw [indicator_of_notMem (show x ∉ {x | 0 < W x} from hx), show W x = 0 from le_antisymm (not_lt.1 hx) a]
    simp

theorem momA : MomA := by
  intro Ω Ω' _ _ ν ν' U U' t0 hU hU' h h' ht he hf
  have p : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → {x | 0 < W x} = {x | 0 < W x ^ t0} := fun W h => by
    ext x
    show 0 < W x ↔ 0 < W x ^ t0
    exact ⟨fun a => pow_pos a _, fun a => (h x).1.lt_of_ne fun b => by
      rw [← b, zero_pow (by omega)] at a; exact lt_irrefl _ a⟩
  have q : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → ∀ x, 0 ≤ W x ^ t0 ∧ W x ^ t0 ≤ 1 := fun W h x =>
    ⟨pow_nonneg (h x).1 _, pow_le_one₀ (h x).1 (h x).2⟩
  rw [p U h, p U' h', mom_sum ν (hU.pow_const t0) (q U h), mom_sum ν' (hU'.pow_const t0) (q U' h')]
  refine tsum_congr fun M => mom_step (hU.pow_const t0) (hU'.pow_const t0) (q U h) (q U' h') (fun j hj => ?_)
    (fun j hj => ?_) M 1 le_rfl
  · simpa only [← pow_mul, mul_comm t0] using he j hj
  · simpa only [← pow_mul, mul_comm t0] using hf j hj

theorem momB : MomB := by
  intro I _ α β c hα hβ hc
  refine ⟨(Measure.pi fun _ : I => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
    fun y => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|)), fun y => ∏ i, Real.exp (-β i * |y i|), by fun_prop,
    fun y => ⟨Finset.prod_pos fun i _ => Real.exp_pos _, Finset.prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ =>
      Real.exp_le_one_iff.2 (by have := hβ i; have := abs_nonneg (y i); nlinarith)⟩, fun t => ?_⟩
  have hp : ∀ i, 0 < α i + t * β i := fun i => by have := hα i; have := hβ i; positivity
  have e1 : ∀ i, EqOn (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (fun x => Real.exp (-(α i + t * β i) * x)) (Ioi 0) :=
    fun i x hx => by simp only [abs_of_pos (show (0 : ℝ) < x from hx)]
  have hi : ∀ i, Integrable (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hp i)) 0).congr_fun (e1 i).symm measurableSet_Ioi
  have hv : ∀ i, ∫ x in Ioi (0 : ℝ), Real.exp (-(α i + t * β i) * |x|) = (α i + t * β i)⁻¹ := fun i => by
    rw [setIntegral_congr_fun measurableSet_Ioi (e1 i), integral_exp_mul_Ioi (neg_neg_of_pos (hp i))]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have e2 : ∀ y : I → ℝ, ((fun y : I → ℝ => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|))) *
      fun y : I → ℝ => ENNReal.ofReal ((∏ i, Real.exp (-β i * |y i|)) ^ t)) y =
      ENNReal.ofReal (c * ∏ i, Real.exp (-(α i + t * β i) * |y i|)) := fun y => by
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [lintegral_congr e2, ← ofReal_integral_eq_lintegral_ofReal ((Integrable.fintype_prod hi).const_mul c)
    (.of_forall fun y => by positivity), integral_const_mul,
    integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Real.exp (-(α i + t * β i) * |x|))]
  simp only [hv, Finset.prod_inv_distrib, div_eq_mul_inv]

theorem momW_of : MomA → MomB → MomW := by
  intro hA hB Ω _ P h U I _ α β c t0 hh hU h01 hα hβ hc hm
  obtain ⟨ν', U', m', p', e'⟩ := hB I α β c hα hβ hc
  have e : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * (t0 + 1))) ∂(P.withDensity h) =
      ENNReal.ofReal (c / ∏ i, (α i + (j * (t0 + 1) : ℕ) * β i)) := fun j hj => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    exact hm _ (by nlinarith)
  have r := hA Ω _ (P.withDensity h) ν' U U' (t0 + 1) hU m' h01 (fun y => ⟨(p' y).1.le, (p' y).2⟩) (by omega)
    (fun j hj => (e j hj).trans (e' _).symm) fun j hj => by rw [e j hj]; exact ENNReal.ofReal_ne_top
  rw [withDensity_apply _ (measurableSet_lt measurable_const hU)] at r
  rw [r, show {y | 0 < U' y} = univ from eq_univ_of_forall fun y => (p' y).1]
  simpa using e' 0

theorem momW : MomW := momW_of momA momB

end CompanionTheory.RgFd
