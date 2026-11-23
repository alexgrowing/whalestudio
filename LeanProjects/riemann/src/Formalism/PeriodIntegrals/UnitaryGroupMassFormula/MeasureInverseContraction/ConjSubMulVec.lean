import Mathlib
import Formalism.PeriodIntegrals.NMeasInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.AmatInvMul

noncomputable section

open Matrix

namespace PI.NMeasInv.UnitaryGroupMassFormula

section Tri

variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}

theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  rw [hJ_conj ε y, hJ_conj ε y x, hJ_conj ε y x', hJ_add, star_add]

theorem Pw_add (x y : Fin n → ℂ) : Pw ε e f (x + y) = Pw ε e f x + Pw ε e f y := by
  simp only [Pw, hJ_add, add_smul, Finset.sum_add_distrib]; abel

theorem Pw_smul (c : ℂ) (x : Fin n → ℂ) : Pw ε e f (c • x) = c • Pw ε e f x := by
  simp only [Pw, hJ_smul, mul_smul, ← Finset.smul_sum, smul_sub]

theorem Pw_zero : Pw ε e f 0 = 0 := by simp [Pw, hJ_zero]

theorem Pw_sum {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) :
    Pw ε e f (∑ i ∈ s, x i) = ∑ i ∈ s, Pw ε e f (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Pw_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Pw_add, ih]

theorem mulVec_fsum {ι : Type*} (s : Finset ι) (M : Matrix (Fin n) (Fin n) ℂ) (x : ι → Fin n → ℂ) :
    M *ᵥ (∑ i ∈ s, x i) = ∑ i ∈ s, M *ᵥ x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mulVec_add, ih]

theorem hJ_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  rw [hJ_mulVec_eq, hg]; rfl

theorem conj_sub_mulVec (hG : Gram ε e f) (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) (g : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) : (Amat ε e f s * g * Amat ε e f s⁻¹ - 1) *ᵥ y =
      Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ y) := by
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Amat_mulVec, Amat_mulVec, sub_mulVec,
    one_mulVec]
  have := (Alin ε e f s).map_sub (g *ᵥ Afun ε e f s⁻¹ y) (Afun ε e f s⁻¹ y)
  simp only [Alin_apply] at this
  rw [this, A_inv hG s hs]

variable (hG : Gram ε e f)
include hG

theorem Pw_e (d : Fin r) : Pw ε e f (e d) = 0 := by
  unfold Pw
  simp only [fe hG, hG.ee, ite_smul, one_smul, zero_smul, Finset.sum_const_zero, sub_zero]
  simp [Finset.sum_ite_eq]

theorem span_facts (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    (∀ b : Fin r, k ≤ b.val → hJ ε (f b) v = 0) ∧ (∀ b, hJ ε (e b) v = 0) ∧ Pw ε e f v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    refine ⟨fun b hb => ?_, fun b => hG.ee b d, Pw_e hG d⟩
    rw [fe hG, if_neg]
    rintro rfl
    exact (not_lt.2 hb) hd
  | zero => exact ⟨fun b _ => hJ_zero ε _, fun b => hJ_zero ε _, Pw_zero⟩
  | add x y _ _ hx hy =>
    exact ⟨fun b hb => by rw [hJ_add, hx.1 b hb, hy.1 b hb, add_zero],
      fun b => by rw [hJ_add, hx.2.1 b, hy.2.1 b, add_zero], by rw [Pw_add, hx.2.2, hy.2.2, add_zero]⟩
  | smul c x _ hx =>
    exact ⟨fun b hb => by rw [hJ_smul, hx.1 b hb, mul_zero], fun b => by rw [hJ_smul, hx.2.1 b, mul_zero],
      by rw [Pw_smul, hx.2.2, smul_zero]⟩

theorem tri_f {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hgg : g * g' = 1)
    (hN' : InN ε e z g') (b c : Fin r) (hbc : ¬ c < b) : hJ ε (e b) ((g - 1) *ᵥ f c) = 0 := by
  rw [sub_mulVec, one_mulVec, hJ_sub]
  have h1 : e b = g *ᵥ (g' *ᵥ e b) := by rw [mulVec_mulVec, hgg, one_mulVec]
  have h2 : g' *ᵥ e b = e b + (g' - 1) *ᵥ e b := by rw [sub_mulVec, one_mulVec]; abel
  have h3 := (span_facts hG b.val (hN'.1.1 b)).1 c (Fin.le_iff_val_le_val.1 (not_lt.1 hbc))
  have key : hJ ε (e b) (g *ᵥ f c) = hJ ε (e b) (f c) := by
    calc hJ ε (e b) (g *ᵥ f c) = hJ ε (g *ᵥ (g' *ᵥ e b)) (g *ᵥ f c) := by rw [← h1]
      _ = hJ ε (g' *ᵥ e b) (f c) := hJ_unitary hg _ _
      _ = hJ ε (e b) (f c) + hJ ε ((g' - 1) *ᵥ e b) (f c) := by rw [h2, hJ_add_left]
      _ = hJ ε (e b) (f c) := by rw [hJ_conj ε (f c) ((g' - 1) *ᵥ e b), h3, star_zero, add_zero]
  rw [key, sub_self]

omit hG in

def Sb (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ)
    (i : Fin n) : ℝ :=
  ∑ b, ((∑ c, ‖hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)‖ +
      ∑ c, ‖hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)‖ +
      ‖hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)‖) * ‖e b i‖) +
    ∑ b, (∑ c, ‖hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)‖) * ‖f b i‖ +
    ∑ c, ‖hJ ε (e c) y‖ * ‖Pw ε e f ((g - 1) *ᵥ f c) i‖

omit hG in
theorem nb {κ lam : ℝ} {x : ℂ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ lam⁻¹ ∨ x = 0) : ‖(κ : ℂ) * x‖ ≤ lam⁻¹ * ‖x‖ := by
  rcases hκ with h | h
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  · simp [h]

theorem entry_bound (t : Fin r → ℝ) (lam : ℝ) (hlam : 1 ≤ lam) (ht1 : ∀ b, lam ≤ t b)
    (ht2 : ∀ b c : Fin r, b < c → lam * t c ≤ t b) {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) (hgg : g * g' = 1) (hN : InN ε e z g) (hN' : InN ε e z g') (y : Fin n → ℂ)
    (i : Fin n) : ‖Afun ε e f t⁻¹ ((g - 1) *ᵥ Afun ε e f t y) i‖ ≤ lam⁻¹ * Sb ε e f g y i := by
  have hl0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have ht0 : ∀ b, 0 < t b := fun b => lt_of_lt_of_le hl0 (ht1 b)

  have hXe := fun c => span_facts hG _ (hN.1.1 c)
  have hXw : ∀ v, (∀ a, hJ ε (e a) v = 0) → (∀ b, hJ ε (e b) ((g - 1) *ᵥ v) = 0) ∧ Pw ε e f ((g - 1) *ᵥ v) = 0 :=
    fun v hv => (span_facts hG _ (hN.2 v hv)).2
  have hPwy : ∀ a, hJ ε (e a) (Pw ε e f y) = 0 := fun a => e_Pw hG a y

  have hv : (g - 1) *ᵥ Afun ε e f t y = ∑ c, ((t c : ℂ) * hJ ε (f c) y) • (g - 1) *ᵥ e c +
      ∑ c, ((t c : ℂ)⁻¹ * hJ ε (e c) y) • (g - 1) *ᵥ f c + (g - 1) *ᵥ Pw ε e f y := by
    rw [Afun, mulVec_add, mulVec_add, mulVec_fsum, mulVec_fsum]
    simp only [mulVec_smul]
  set w := (g - 1) *ᵥ Afun ε e f t y with hw
  have hα : ∀ b, hJ ε (f b) w = ∑ c, (t c : ℂ) * (hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)) +
      ∑ c, (t c : ℂ)⁻¹ * (hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)) + hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y) := by
    intro b
    rw [hv, hJ_add, hJ_add, hJ_sum, hJ_sum]
    simp only [hJ_smul, mul_assoc]
  have hβ : ∀ b, hJ ε (e b) w = ∑ c, (t c : ℂ)⁻¹ * (hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)) := by
    intro b
    rw [hv, hJ_add, hJ_add, hJ_sum, hJ_sum, (hXw _ hPwy).1 b]
    simp only [hJ_smul, (hXe _).2.1 b, mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_assoc]
  have hP : Pw ε e f w = ∑ c, ((t c : ℂ)⁻¹ * hJ ε (e c) y) • Pw ε e f ((g - 1) *ᵥ f c) := by
    rw [hv, Pw_add, Pw_add, Pw_sum, Pw_sum, (hXw _ hPwy).2]
    simp only [Pw_smul, (hXe _).2.2, smul_zero, Finset.sum_const_zero, zero_add, add_zero]

  have hent : Afun ε e f t⁻¹ w i =
      ∑ b, (∑ c, (((t c / t b : ℝ) : ℂ) * (hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c))) +
        ∑ c, ((((t c * t b)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c))) +
        (((t b)⁻¹ : ℝ) : ℂ) * hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)) * e b i +
      ∑ b, (∑ c, (((t b / t c : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)))) * f b i +
      ∑ c, (((t c)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * Pw ε e f ((g - 1) *ᵥ f c) i) := by
    rw [Afun, hP]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hα, hβ, Pi.inv_apply,
      Complex.ofReal_inv, inv_inv]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      congr 1
      · refine Finset.sum_congr rfl fun c _ => ?_
        push_cast; ring
      · refine Finset.sum_congr rfl fun c _ => ?_
        push_cast; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      push_cast; ring
    · refine Finset.sum_congr rfl fun c _ => ?_
      push_cast; ring
  rw [hent]

  have k1 : ∀ b c : Fin r, ‖(((t c / t b : ℝ) : ℂ) * (hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)))‖ ≤
      lam⁻¹ * ‖hJ ε (f c) y * hJ ε (f b) ((g - 1) *ᵥ e c)‖ := by
    intro b c
    refine nb (div_nonneg (ht0 c).le (ht0 b).le) ?_
    by_cases hbc : b < c
    · left
      rw [div_le_iff₀ (ht0 b)]
      have := ht2 b c hbc
      calc t c = lam⁻¹ * (lam * t c) := by field_simp
        _ ≤ lam⁻¹ * t b := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hl0.le)
    · right
      rw [(hXe c).1 b (Fin.le_iff_val_le_val.1 (not_lt.1 hbc)), mul_zero]
  have k2 : ∀ b c : Fin r, ‖((((t c * t b)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)))‖ ≤
      lam⁻¹ * ‖hJ ε (e c) y * hJ ε (f b) ((g - 1) *ᵥ f c)‖ := by
    intro b c
    refine nb (inv_nonneg.2 (mul_nonneg (ht0 c).le (ht0 b).le)) (Or.inl ?_)
    apply inv_anti₀ hl0
    calc lam = 1 * lam := (one_mul _).symm
      _ ≤ t c * t b := mul_le_mul (hlam.trans (ht1 c)) (ht1 b) hl0.le (ht0 c).le
  have k3 : ∀ b : Fin r, ‖((((t b)⁻¹ : ℝ) : ℂ) * hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y))‖ ≤
      lam⁻¹ * ‖hJ ε (f b) ((g - 1) *ᵥ Pw ε e f y)‖ := fun b =>
    nb (inv_nonneg.2 (ht0 b).le) (Or.inl (inv_anti₀ hl0 (ht1 b)))
  have k4 : ∀ b c : Fin r, ‖(((t b / t c : ℝ) : ℂ) * (hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)))‖ ≤
      lam⁻¹ * ‖hJ ε (e c) y * hJ ε (e b) ((g - 1) *ᵥ f c)‖ := by
    intro b c
    refine nb (div_nonneg (ht0 b).le (ht0 c).le) ?_
    by_cases hcb : c < b
    · left
      rw [div_le_iff₀ (ht0 c)]
      have := ht2 c b hcb
      calc t b = lam⁻¹ * (lam * t b) := by field_simp
        _ ≤ lam⁻¹ * t c := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hl0.le)
    · right
      rw [tri_f hG hg hgg hN' b c hcb, mul_zero]
  have k5 : ∀ c : Fin r, ‖((((t c)⁻¹ : ℝ) : ℂ) * (hJ ε (e c) y * Pw ε e f ((g - 1) *ᵥ f c) i))‖ ≤
      lam⁻¹ * (‖hJ ε (e c) y‖ * ‖Pw ε e f ((g - 1) *ᵥ f c) i‖) := by
    intro c
    rw [← norm_mul]
    exact nb (inv_nonneg.2 (ht0 c).le) (Or.inl (inv_anti₀ hl0 (ht1 c)))

  unfold Sb
  simp only [mul_add, Finset.mul_sum]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [mul_add]
    refine add_le_add ((norm_add_le _ _).trans ?_) (k3 b)
    rw [mul_add]
    refine add_le_add ((norm_sum_le _ _).trans ?_) ((norm_sum_le _ _).trans ?_)
    · rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => k1 b c
    · rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => k2 b c
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => k4 b c
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    exact k5 c

end Tri

end PI.NMeasInv.UnitaryGroupMassFormula
