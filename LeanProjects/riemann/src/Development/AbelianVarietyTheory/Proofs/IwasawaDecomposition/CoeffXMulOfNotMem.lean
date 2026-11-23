import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions

noncomputable section

open Matrix MvPowerSeries GlobalTheory.FockSeq

namespace GlobalTheory.GaussInner

variable {σ : Type} [DecidableEq σ]

theorem coeff_X_mul_add (l : σ) (E : MvPowerSeries σ ℂ) (β : σ →₀ ℕ) :
    coeff (β + Finsupp.single l 1) (X l * E) = coeff β E := by
  rw [X_def, add_comm, coeff_add_monomial_mul, one_mul]

theorem coeff_X_mul_of_notMem (l : σ) (E : MvPowerSeries σ ℂ) {α : σ →₀ ℕ}
    (h : α ∉ Set.range fun β : σ →₀ ℕ => β + Finsupp.single l 1) : α l = 0 ∧ coeff α (X l * E) = 0 := by
  have h' : ¬ Finsupp.single l 1 ≤ α := fun hle => h ⟨_, tsub_add_cancel_of_le hle⟩
  refine ⟨by rw [Finsupp.single_le_iff] at h'; omega, ?_⟩
  rw [X_def, coeff_monomial_mul, if_neg h']

def dil (σ : Type) : Submodule ℂ (MvPowerSeries σ ℂ) where
  carrier := {E | ∀ r : ℝ, 0 ≤ r → r < 1 →
    Summable fun α : σ →₀ ℕ => r ^ α.degree * ((mfact α : ℝ) * ‖coeff α E‖ ^ 2)}
  zero_mem' r _ _ := by simp
  add_mem' {E E'} h h' r h0 h1 := by
    refine .of_nonneg_of_le (fun α => by positivity) (fun α => ?_) (((h r h0 h1).add (h' r h0 h1)).mul_left 2)
    rw [map_add, ← mul_add, ← mul_add, mul_left_comm 2, mul_left_comm 2]
    gcongr
    nlinarith [norm_add_le (coeff α E) (coeff α E'), norm_nonneg (coeff α E + coeff α E'),
      sq_nonneg (‖coeff α E‖ - ‖coeff α E'‖)]
  smul_mem' c E h r h0 h1 := by
    refine ((h r h0 h1).mul_left (‖c‖ ^ 2)).congr fun α => ?_
    rw [coeff_smul, norm_mul]; ring

theorem X_mul_mem {E : MvPowerSeries σ ℂ} (h : E ∈ dil σ) (l : σ) : X l * E ∈ dil σ := by
  intro r h0 h1
  have hρ0 := Real.sqrt_nonneg r
  have hρ1 : √r < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using h1)
  obtain ⟨C, hC⟩ := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).bddAbove_range
  rw [← (add_left_injective (Finsupp.single l 1)).summable_iff
    fun α hα => by simp [(coeff_X_mul_of_notMem l E hα).2]]
  refine .of_nonneg_of_le (fun α => by dsimp; positivity) (fun β => ?_) ((h _ hρ0 hρ1).mul_left C)
  have h2 : ((β.degree + 1 : ℕ) : ℝ) * √r ^ (β.degree + 1) ≤ C := hC ⟨_, rfl⟩
  have h3 : (β l : ℝ) ≤ β.degree := Nat.cast_le.2 (Finsupp.le_degree l β)
  have h4 : r ^ (β.degree + 1) = √r ^ (β.degree + 1) * √r ^ (β.degree + 1) := by
    rw [← mul_pow, Real.mul_self_sqrt h0]
  have h5 : √r ^ (β.degree + 1) ≤ √r ^ β.degree := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ _)
  simp only [Function.comp, coeff_X_mul_add, map_add, Finsupp.degree_single, Oscillator.mfact_add_single, h4]
  push_cast at h2 ⊢
  calc _ = (((β l : ℝ) + 1) * √r ^ (β.degree + 1)) *
        (√r ^ (β.degree + 1) * ((mfact β : ℝ) * ‖coeff β E‖ ^ 2)) := by ring
    _ ≤ (((β.degree : ℝ) + 1) * √r ^ (β.degree + 1)) *
        (√r ^ β.degree * ((mfact β : ℝ) * ‖coeff β E‖ ^ 2)) := by gcongr
    _ ≤ _ := by gcongr

def mulX (l : σ) : dil σ →ₗ[ℂ] dil σ := (LinearMap.mulLeft ℂ (X l)).restrict fun _ h => X_mul_mem h l

@[simp] theorem coe_mulX (l : σ) (E : dil σ) : (mulX l E : MvPowerSeries σ ℂ) = X l * (E : MvPowerSeries σ ℂ) := rfl

def term (t : ℝ) (E E' : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) : ℂ :=
  (t : ℂ) ^ α.degree * ((mfact α : ℂ) * coeff α E * coeff α E')

omit [DecidableEq σ] in

theorem norm_term_le {t : ℝ} (ht : 0 ≤ t) (E E' : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) :
    ‖term t E E' α‖ ≤ t ^ α.degree * ((mfact α : ℝ) * ‖coeff α E‖ ^ 2) +
      t ^ α.degree * ((mfact α : ℝ) * ‖coeff α E'‖ ^ 2) := by
  rw [term, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht,
    Complex.norm_natCast, ← mul_add, ← mul_add, mul_assoc]
  gcongr
  nlinarith [sq_nonneg (‖coeff α E‖ - ‖coeff α E'‖), norm_nonneg (coeff α E), norm_nonneg (coeff α E')]

omit [DecidableEq σ] in

theorem summable_norm_term {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (E E' : dil σ) :
    Summable fun α => ‖term t E.1 E'.1 α‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le ht.1.le _ _)
    ((E.2 t ht.1.le ht.2).add (E'.2 t ht.1.le ht.2))

def pr {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : dil σ →ₗ[ℂ] dil σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun E E' => ∑' α, term t E.1 E'.1 α)
    (fun E₁ E₂ E' => by
      rw [← (summable_norm_term ht E₁ E').of_norm.tsum_add (summable_norm_term ht E₂ E').of_norm]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_add, map_add]; ring)
    (fun c E E' => by
      rw [smul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_smul, coeff_smul]; ring)
    (fun E E₁ E₂ => by
      rw [← (summable_norm_term ht E E₁).of_norm.tsum_add (summable_norm_term ht E E₂).of_norm]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_add, map_add]; ring)
    (fun c E E' => by
      rw [smul_eq_mul, ← tsum_mul_left]
      exact tsum_congr fun α => by simp only [term, Submodule.coe_smul, coeff_smul]; ring)

variable {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)

omit [DecidableEq σ] in

theorem pr_apply (E E' : dil σ) : pr ht E E' = ∑' α, term t E.1 E'.1 α := rfl

omit [DecidableEq σ] in

theorem pr_comm (E E' : dil σ) : pr ht E E' = pr ht E' E :=
  tsum_congr fun α => by simp only [term]; ring

def IsPDer (l : σ) (E D : MvPowerSeries σ ℂ) : Prop :=
  ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E = coeff α D

theorem pr_mulX {l : σ} (E : dil σ) {E' D : dil σ} (h : IsPDer l E'.1 D.1) :
    pr ht (mulX l E) E' = t * pr ht E D := by
  rw [pr_apply, pr_apply, ← (add_left_injective (Finsupp.single l 1)).tsum_eq
    (fun α hα => by
      by_contra h'
      exact hα (by simp [term, (coeff_X_mul_of_notMem l _ h').2])), ← tsum_mul_left]
  refine tsum_congr fun β => ?_
  simp only [term, coe_mulX, coeff_X_mul_add, map_add, Finsupp.degree_single, Oscillator.mfact_add_single, ← h β]
  push_cast
  ring

theorem IsPDer.coeff_X_mul {l : σ} {E D : MvPowerSeries σ ℂ} (h : IsPDer l E D) (α : σ →₀ ℕ) :
    coeff α (X l * D) = (α l : ℂ) * coeff α E := by
  by_cases hα : α ∈ Set.range fun β : σ →₀ ℕ => β + Finsupp.single l 1
  · obtain ⟨β, rfl⟩ := hα
    simp [coeff_X_mul_add, ← h β]
  · simp [coeff_X_mul_of_notMem l D hα]

theorem IsPDer.X_mul {k : σ} {E D : MvPowerSeries σ ℂ} (h : IsPDer k E D) (m : σ) :
    IsPDer k (X m * E) (X m * D + (if k = m then (1 : ℂ) else 0) • E) := by
  intro α
  by_cases hk : k = m
  · subst hk
    rw [coeff_X_mul_add, map_add, h.coeff_X_mul]; simp; ring
  rw [if_neg hk, zero_smul, add_zero]
  by_cases hα : α ∈ Set.range fun β : σ →₀ ℕ => β + Finsupp.single m 1
  · obtain ⟨β, rfl⟩ := hα
    simp only
    rw [coeff_X_mul_add, add_right_comm, coeff_X_mul_add, ← h β]
    simp [Finsupp.single_apply, Ne.symm hk]
  · obtain ⟨h1, h2⟩ := coeff_X_mul_of_notMem m D hα
    rw [h2, (coeff_X_mul_of_notMem m E _).2, mul_zero]
    rintro ⟨β, hβ⟩
    have := congrArg (fun γ : σ →₀ ℕ => γ m) hβ
    simp [h1, hk] at this

variable [Fintype σ]

theorem hasDerivAt_pairing (E E' : dil σ) (D D' : σ → dil σ)
    (h : ∀ l, IsPDer l E.1 (D l).1) (h' : ∀ l, IsPDer l E'.1 (D' l).1) :
    HasDerivAt (fun s : ℝ => ∑' α, term s E.1 E'.1 α) (∑ l, pr ht (D l) (D' l)) t := by
  have hterm : ∀ s α, ∑ l, term s (mulX l (D l)).1 E'.1 α = (α.degree : ℂ) * term s E.1 E'.1 α := fun s α => by
    simp only [term, coe_mulX, (h _).coeff_X_mul, Finsupp.degree_eq_sum]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨r, htr, hr1⟩ := exists_between ht.2
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1.trans htr, hr1⟩
  have hsum : Summable fun α : σ →₀ ℕ => r⁻¹ * ‖(α.degree : ℂ) * term r E.1 E'.1 α‖ := by
    refine Summable.mul_left _ ?_
    simp only [← hterm]
    exact (summable_sum fun l _ => (summable_norm_term hr (mulX l (D l)) E').of_norm).norm
  set c : (σ →₀ ℕ) → ℂ := fun α => (mfact α : ℂ) * coeff α (E : MvPowerSeries σ ℂ) *
    coeff α (E' : MvPowerSeries σ ℂ) with hc
  have hpow : ∀ s : ℝ, s ≠ 0 → ∀ n : ℕ, (n : ℂ) * (s : ℂ) ^ (n - 1) = (s : ℂ)⁻¹ * (n * (s : ℂ) ^ n) := by
    intro s hs n
    have : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; field_simp
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun α (s : ℝ) => term s E.1 E'.1 α)
    (g' := fun α (s : ℝ) => (α.degree : ℂ) * (s : ℂ) ^ (α.degree - 1) * c α) hsum isOpen_Ioo
    (isPreconnected_Ioo (a := 0) (b := r))
    (fun α s _ => ((hasDerivAt_pow α.degree (s : ℂ)).comp_ofReal).mul_const (c α))
    (fun α s hs => by
      have e : r⁻¹ * ‖(α.degree : ℂ) * term r E.1 E'.1 α‖ = ‖(α.degree : ℂ) * (r : ℂ) ^ (α.degree - 1) * c α‖ := by
        rw [hpow r hr.1.ne', mul_assoc, mul_assoc, norm_mul (r : ℂ)⁻¹, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg hr.1.le]
        rfl
      rw [e]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.1.le, Real.norm_of_nonneg hs.1.le]
      gcongr
      exacts [hs.1.le, hs.2.le])
    ⟨ht.1, htr⟩ (summable_norm_term ht E E').of_norm ⟨ht.1, htr⟩
  refine key.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.1.ne'
  apply mul_left_cancel₀ ht0
  rw [Finset.mul_sum, ← tsum_mul_left]
  simp only [← fun l => pr_mulX ht (D l) (h' l)]
  simp only [pr_apply]
  rw [← Summable.tsum_finsetSum fun l _ => (summable_norm_term ht (mulX l (D l)) E').of_norm]
  refine tsum_congr fun α => ?_
  rw [hterm, hpow t ht.1.ne', term]
  simp only [hc]
  field_simp

theorem moments : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ) (E E' : MvPowerSeries σ ℂ), Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α E‖ ^ 2) → Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α E'‖ ^ 2) → (∀ l α, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E = coeff α (x l • E + ∑ k, S l k • (X k * E))) → (∀ l α, ((α l : ℂ) + 1) * coeff (α + Finsupp.single l 1) E' = coeff α (y l • E' + ∑ k, T l k • (X k * E'))) → let f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree * ((mfact α : ℂ) * coeff α E * coeff α E'); ContinuousOn f (Set.Icc 0 1) ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ (p q : σ → ℂ) (m n : Matrix σ σ ℂ), p = (t : ℂ) • (f t • y + T *ᵥ q) ∧ q = (t : ℂ) • (f t • x + S *ᵥ p) ∧ m = ((t : ℂ) * f t) • (1 : Matrix σ σ ℂ) + (t : ℂ) • vecMulVec y q + (t : ℂ) • (T * n) ∧ n = (t : ℂ) • vecMulVec x q + (t : ℂ) • (S * m) ∧ HasDerivAt f (f t * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace) t := by
  intro σ _ _ S T x y E E' hE hE' hd hd' f
  have hm : ∀ {G : MvPowerSeries σ ℂ}, Summable (fun α : σ →₀ ℕ => (mfact α : ℝ) * ‖coeff α G‖ ^ 2) →
      G ∈ dil σ := fun hG r h0 h1 =>
    .of_nonneg_of_le (fun α => by positivity)
      (fun α => mul_le_of_le_one_left (by positivity) (pow_le_one₀ h0 h1.le)) hG
  refine ⟨continuousOn_tsum (fun α => by fun_prop) (hE.add hE') fun α s hs => ?_, fun t ht => ?_⟩
  · refine (norm_term_le hs.1 E E' α).trans (add_le_add ?_ ?_) <;>
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hs.1 hs.2)
  let e : dil σ := ⟨E, hm hE⟩
  let e' : dil σ := ⟨E', hm hE'⟩
  have hD : ∀ l, IsPDer l (e : MvPowerSeries σ ℂ) (x l • e + ∑ k, S l k • mulX k e : dil σ).1 := fun l α => by
    simpa [e] using hd l α
  have hD' : ∀ l, IsPDer l (e' : MvPowerSeries σ ℂ) (y l • e' + ∑ k, T l k • mulX k e' : dil σ).1 :=
    fun l α => by simpa [e'] using hd' l α
  have hf : f t = pr ht e e' := rfl
  refine ⟨fun l => pr ht (mulX l e) e', fun l => pr ht e (mulX l e'),
    .of fun k m => pr ht (mulX k e) (mulX m e'), .of fun k m => pr ht e (mulX k (mulX m e')), ?_, ?_, ?_, ?_, ?_⟩
  · ext l
    simp [pr_mulX ht _ (hD' l), hf, mulVec, dotProduct, mul_comm]
  · ext l
    rw [pr_comm, pr_mulX ht _ (hD l), pr_comm]
    simp [hf, mulVec, dotProduct, mul_comm]
  · ext k m
    have h1 : IsPDer k (mulX m e' : MvPowerSeries σ ℂ) (mulX m (y k • e' + ∑ j, T k j • mulX j e') +
      (if k = m then (1 : ℂ) else 0) • e' : dil σ).1 := (hD' k).X_mul m
    have h2 : ∀ j, mulX m (mulX j e') = mulX j (mulX m e') := fun j => Subtype.ext (by simp [mul_left_comm])
    rw [of_apply, pr_mulX ht _ h1]
    by_cases hk : k = m <;> simp [hf, h2, hk, Matrix.mul_apply, vecMulVec_apply] <;> ring
  · ext k m
    rw [of_apply, pr_comm, pr_mulX ht _ (hD k), pr_comm]
    simp [Matrix.mul_apply, vecMulVec_apply, mul_add]
  · refine (hasDerivAt_pairing ht e e' _ _ hD hD').congr_deriv ?_
    simp only [hf, mulVec, dotProduct, trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply, of_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have h1 : ∀ (g : σ → ℂ) (G : σ → σ → ℂ) (c : ℂ), ∑ m, T l m * (c * g m + ∑ k, S l k * G k m) =
        c * ∑ m, T l m * g m + ∑ m, (∑ k, S l k * G k m) * T l m := fun g G c => by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [h1 (fun m => pr ht e (mulX m e')) (fun k m => pr ht (mulX k e) (mulX m e'))]
    ring

end GlobalTheory.GaussInner
