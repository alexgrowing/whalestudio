import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Imports

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

section
variable {M ι : Type*} (G : ι → (M → ℂ))

theorem cont_span {Y : Type*} [TopologicalSpace Y] (φ : Y → M) (hG : ∀ p, Continuous fun y => G p (φ y)) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), Continuous fun y => f (φ y) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

theorem dom_span {β : Type*} (L R : β → M)
    (hG : ∀ p, ∃ (T : Finset ι) (Cf : ℝ), ∀ b, ‖G p (L b)‖ ^ 2 ≤ Cf * ∑ q ∈ T, ‖G q (R b)‖ ^ 2) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ∃ (T : Finset (M → ℂ)) (Cf : ℝ),
      (∀ h ∈ T, h ∈ Submodule.span ℂ (Set.range G)) ∧ ∀ b, ‖f (L b)‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (R b)‖ ^ 2 := by
  classical
  set S := Submodule.span ℂ (Set.range G)
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨T, Cf, hT⟩ := hG p
    obtain ⟨T', hT'S, hT'⟩ := absorb S T G (fun q _ => Submodule.subset_span ⟨q, rfl⟩) 2 (by norm_num)
    refine ⟨T', max Cf 0, hT'S, fun b => ?_⟩
    have h0 : 0 ≤ ∑ q ∈ T, ‖G q (R b)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    calc ‖G p (L b)‖ ^ 2 ≤ Cf * ∑ q ∈ T, ‖G q (R b)‖ ^ 2 := hT b
      _ ≤ max Cf 0 * ∑ q ∈ T, ‖G q (R b)‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ max Cf 0 * ∑ h ∈ T', ‖h (R b)‖ ^ 2 := mul_le_mul_of_nonneg_left (hT' _) (le_max_right _ _)
  | zero => exact ⟨∅, 0, by simp, fun b => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, C₁, h₁S, h₁⟩ := hx
    obtain ⟨T₂, C₂, h₂S, h₂⟩ := hy
    set c : ℝ := Real.sqrt (2 * max (max C₁ C₂) 0)
    have hc2 : c ^ 2 = 2 * max (max C₁ C₂) 0 := Real.sq_sqrt (by positivity)
    obtain ⟨T, hTS, hT⟩ := absorb S (T₁.disjSum T₂) (fun s => (c : ℂ) • Sum.elim id id s)
      (fun s hs => by
        rcases s with s | s
        · exact S.smul_mem _ (h₁S s (Finset.inl_mem_disjSum.mp hs))
        · exact S.smul_mem _ (h₂S s (Finset.inr_mem_disjSum.mp hs))) 2 (by norm_num)
    refine ⟨T, 1, hTS, fun b => ?_⟩
    have e1 := h₁ b
    have e2 := h₂ b
    have s1 : 0 ≤ ∑ h ∈ T₁, ‖h (R b)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have s2 : 0 ≤ ∑ h ∈ T₂, ‖h (R b)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hK := hT (R b)
    rw [Finset.sum_disjSum] at hK
    simp only [Sum.elim_inl, Sum.elim_inr, id, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hc2, ← Finset.mul_sum] at hK
    have hm : ‖x (L b) + y (L b)‖ ^ 2 ≤ 2 * ‖x (L b)‖ ^ 2 + 2 * ‖y (L b)‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (x (L b)) (y (L b))) 2
      nlinarith [sq_nonneg (‖x (L b)‖ - ‖y (L b)‖)]
    have q1 : ‖x (L b)‖ ^ 2 ≤ max (max C₁ C₂) 0 * ∑ h ∈ T₁, ‖h (R b)‖ ^ 2 :=
      e1.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) s1)
    have q2 : ‖y (L b)‖ ^ 2 ≤ max (max C₁ C₂) 0 * ∑ h ∈ T₂, ‖h (R b)‖ ^ 2 :=
      e2.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) s2)
    show ‖x (L b) + y (L b)‖ ^ 2 ≤ 1 * ∑ h ∈ T, ‖h (R b)‖ ^ 2
    nlinarith
  | smul a x _ hx =>
    obtain ⟨T₁, C₁, h₁S, h₁⟩ := hx
    refine ⟨T₁, ‖a‖ ^ 2 * C₁, h₁S, fun b => ?_⟩
    show ‖a * x (L b)‖ ^ 2 ≤ _
    rw [norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h₁ b) (by positivity)
end

theorem enorm_add_sq_le (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem lint_add_lt {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : α → ℂ) (w : α → ℝ≥0∞)
    (hf : AEMeasurable (fun a => ‖f a‖ₑ ^ 2 * w a) μ)
    (hF : ∫⁻ a, ‖f a‖ₑ ^ 2 * w a ∂μ < ⊤) (hG : ∫⁻ a, ‖g a‖ₑ ^ 2 * w a ∂μ < ⊤) :
    ∫⁻ a, ‖f a + g a‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  calc ∫⁻ a, ‖f a + g a‖ₑ ^ 2 * w a ∂μ ≤ ∫⁻ a, 2 * (‖f a‖ₑ ^ 2 * w a) + 2 * (‖g a‖ₑ ^ 2 * w a) ∂μ := by
        apply lintegral_mono
        intro a
        calc ‖f a + g a‖ₑ ^ 2 * w a ≤ (2 * ‖f a‖ₑ ^ 2 + 2 * ‖g a‖ₑ ^ 2) * w a := by
              gcongr; exact enorm_add_sq_le _ _
          _ = 2 * (‖f a‖ₑ ^ 2 * w a) + 2 * (‖g a‖ₑ ^ 2 * w a) := by ring
    _ = 2 * ∫⁻ a, ‖f a‖ₑ ^ 2 * w a ∂μ + 2 * ∫⁻ a, ‖g a‖ₑ ^ 2 * w a ∂μ := by
        rw [lintegral_add_left' (hf.const_mul 2), lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ < ⊤ := by
        apply ENNReal.add_lt_top.mpr
        exact ⟨ENNReal.mul_lt_top (by simp) hF, ENNReal.mul_lt_top (by simp) hG⟩

theorem lint_smul_lt {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℂ) (f : α → ℂ) (w : α → ℝ≥0∞)
    (hF : ∫⁻ a, ‖f a‖ₑ ^ 2 * w a ∂μ < ⊤) : ∫⁻ a, ‖c * f a‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  have : ∀ a, ‖c * f a‖ₑ ^ 2 * w a = ‖c‖ₑ ^ 2 * (‖f a‖ₑ ^ 2 * w a) := fun a => by
    rw [enorm_mul, mul_pow, mul_assoc]
  simp_rw [this]
  rw [lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.mul_lt_top (by simp) hF

section
variable {M ι : Type*} (G : ι → (M → ℂ))

theorem lint_span {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ : α → M) (w : α → ℝ≥0∞)
    (hm : ∀ f ∈ Submodule.span ℂ (Set.range G), AEMeasurable (fun a => ‖f (φ a)‖ₑ ^ 2 * w a) μ)
    (hG : ∀ p, ∫⁻ a, ‖G p (φ a)‖ₑ ^ 2 * w a ∂μ < ⊤) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ∫⁻ a, ‖f (φ a)‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero => simp
  | add x y hx' _ hx hy => exact lint_add_lt (fun a => x (φ a)) (fun a => y (φ a)) w (hm x hx') hx hy
  | smul a x _ hx => exact lint_smul_lt a (fun b => x (φ b)) w hx

theorem ae_lint_span {β α : Type*} [MeasurableSpace β] [MeasurableSpace α] (ν : Measure β) (μ : Measure α)
    (φ : β → α → M) (w : α → ℝ≥0∞)
    (hm : ∀ f ∈ Submodule.span ℂ (Set.range G), ∀ x, AEMeasurable (fun a => ‖f (φ x a)‖ₑ ^ 2 * w a) μ)
    (hG : ∀ p, ∀ᵐ x ∂ν, ∫⁻ a, ‖G p (φ x a)‖ₑ ^ 2 * w a ∂μ < ⊤) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ∀ᵐ x ∂ν, ∫⁻ a, ‖f (φ x a)‖ₑ ^ 2 * w a ∂μ < ⊤ := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero => exact Filter.Eventually.of_forall fun x => by simp
  | add x y hx' _ hx hy =>
    filter_upwards [hx, hy] with b h1 h2
    exact lint_add_lt (fun a => x (φ b a)) (fun a => y (φ b a)) w (hm x hx' b) h1 h2
  | smul a x _ hx =>
    filter_upwards [hx] with b h1
    exact lint_smul_lt a (fun c => x (φ b c)) w h1
end

def ChainQ {n : ℕ} (ε : Fin n → Bool) (S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (m : ℕ) (z : Fin m → ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ F : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k, F k ∈ S) ∧ F (Fin.last m) = f ∧
    (∀ (k : Fin m) (g : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), ReciprocityTheory.ChartRestriction.DS.inUJ ε g →
      HasDerivAt (fun s : ℝ => F k.succ (g * aT A s)) (z k * F k.succ (g * aT A t) + F k.castSucc (g * aT A t)) t) ∧
    ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ h ∈ T, h ∈ S) ∧
      ∀ x : PSub ε A, 0 ≤ τ x → ‖F 0 (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖

theorem chain_span {n : ℕ} {ι : Type*} (G : ι → (Matrix (Fin n) (Fin n) ℂ → ℂ)) (ε : Fin n → Bool)
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (m : ℕ) (z : Fin m → ℂ)
    (hG : ∀ p, ChainQ ε (Submodule.span ℂ (Set.range G)) A τ m z (G p)) :
    ∀ f ∈ Submodule.span ℂ (Set.range G), ChainQ ε (Submodule.span ℂ (Set.range G)) A τ m z f := by
  classical
  set S := Submodule.span ℂ (Set.range G)
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hG p
  | zero =>
    refine ⟨fun _ => 0, fun _ => S.zero_mem, rfl, fun k g t _ => ?_, ∅, by simp, fun x _ => by simp⟩
    simpa using hasDerivAt_const t (0 : ℂ)
  | add x y _ _ hx hy =>
    obtain ⟨F₁, h₁S, h₁l, h₁d, T₁, hT₁S, hT₁⟩ := hx
    obtain ⟨F₂, h₂S, h₂l, h₂d, T₂, hT₂S, hT₂⟩ := hy
    obtain ⟨T, hTS, hT⟩ := absorb S (T₁.disjSum T₂) (fun s => Sum.elim id id s)
      (fun s hs => by
        rcases s with s | s
        · exact hT₁S s (Finset.inl_mem_disjSum.mp hs)
        · exact hT₂S s (Finset.inr_mem_disjSum.mp hs)) 1 le_rfl
    refine ⟨F₁ + F₂, fun k => S.add_mem (h₁S k) (h₂S k), by rw [Pi.add_apply, h₁l, h₂l], fun k g t hg => ?_,
      T, hTS, fun x hx => ?_⟩
    · exact ((h₁d k g t hg).add (h₂d k g t hg)).congr_deriv (by simp only [Pi.add_apply]; ring)
    · have hK := hT (S7.toM (x : S7.UJ ε))
      rw [Finset.sum_disjSum] at hK
      simp only [Sum.elim_inl, Sum.elim_inr, id, pow_one] at hK
      have e1 := hT₁ x hx
      have e2 := hT₂ x hx
      have hp : 0 < Real.exp (-τ x) := Real.exp_pos _
      calc ‖(F₁ + F₂) 0 (S7.toM (x : S7.UJ ε))‖
          ≤ ‖F₁ 0 (S7.toM (x : S7.UJ ε))‖ + ‖F₂ 0 (S7.toM (x : S7.UJ ε))‖ := by
            rw [Pi.add_apply, Pi.add_apply]; exact norm_add_le _ _
        _ ≤ Real.exp (-τ x) * (∑ h ∈ T₁, ‖h (S7.toM (x : S7.UJ ε))‖ + ∑ h ∈ T₂, ‖h (S7.toM (x : S7.UJ ε))‖) := by
            rw [mul_add]; exact add_le_add e1 e2
        _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := mul_le_mul_of_nonneg_left hK hp.le
  | smul a x _ hx =>
    obtain ⟨F₁, h₁S, h₁l, h₁d, T₁, hT₁S, hT₁⟩ := hx
    obtain ⟨T, hTS, hT⟩ := absorb S T₁ (fun h => a • h) (fun h hh => S.smul_mem _ (hT₁S h hh)) 1 le_rfl
    refine ⟨a • F₁, fun k => S.smul_mem _ (h₁S k), by rw [Pi.smul_apply, h₁l], fun k g t hg => ?_,
      T, hTS, fun x hx => ?_⟩
    · exact ((h₁d k g t hg).const_mul a).congr_deriv (by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    · have hK := hT (S7.toM (x : S7.UJ ε))
      simp only [pow_one, Pi.smul_apply, smul_eq_mul, norm_mul] at hK
      have e1 := hT₁ x hx
      have hp : 0 < Real.exp (-τ x) := Real.exp_pos _
      calc ‖(a • F₁) 0 (S7.toM (x : S7.UJ ε))‖ = ‖a‖ * ‖F₁ 0 (S7.toM (x : S7.UJ ε))‖ := by
            rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
        _ ≤ ‖a‖ * (Real.exp (-τ x) * ∑ h ∈ T₁, ‖h (S7.toM (x : S7.UJ ε))‖) :=
            mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
        _ = Real.exp (-τ x) * ∑ h ∈ T₁, ‖a‖ * ‖h (S7.toM (x : S7.UJ ε))‖ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := mul_le_mul_of_nonneg_left hK hp.le

end CompanionTheory.RgExh.Dec.L.SA
