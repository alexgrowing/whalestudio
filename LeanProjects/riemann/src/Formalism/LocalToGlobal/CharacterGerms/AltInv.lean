import Mathlib

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))

def IntC (x : C) : Prop := 0 ≤ v x

def IntS {σ : Type*} (f : MvPowerSeries σ C) : Prop := ∀ μ, IntC v (coeff μ f)

variable {v}

theorem intC_zero : IntC v 0 := by
  unfold IntC
  simp
theorem intC_one : IntC v 1 := by
  unfold IntC
  simp
theorem intC_add {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)
theorem intC_neg {x : C} (hx : IntC v x) : IntC v (-x) := by
  unfold IntC at *
  rwa [AddValuation.map_neg]
theorem intC_mul {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x * y) := by
  unfold IntC at *
  rw [AddValuation.map_mul]
  exact add_nonneg hx hy
theorem intC_sub {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x - y) := by
  rw [sub_eq_add_neg]
  exact intC_add hx (intC_neg hy)
theorem intC_natCast (n : ℕ) : IntC v (n : C) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact intC_zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact intC_add ih intC_one
theorem intC_intCast (n : ℤ) : IntC v (n : C) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact intC_natCast n
  | negSucc n =>
    rw [Int.cast_negSucc]
    exact intC_neg (intC_natCast _)
theorem intC_sum {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (IntC v) (fun _ _ => intC_add) intC_zero h
theorem intC_prod {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntC v) (fun _ _ => intC_mul) intC_one h
theorem intC_finsum {ι : Type*} {f : ι → C} (h : ∀ i, IntC v (f i)) : IntC v (∑ᶠ i, f i) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact intC_sum _ fun i _ => h i
  · rw [finsum_of_infinite_support hs]
    exact intC_zero

variable {σ τ : Type*}

theorem intS_mul {f g : MvPowerSeries σ C} (hf : IntS v f) (hg : IntS v g) : IntS v (f * g) := by
  intro μ
  rw [coeff_mul]
  exact intC_sum _ fun p _ => intC_mul (hf _) (hg _)

theorem intS_one : IntS v (1 : MvPowerSeries σ C) := by
  intro μ
  rw [coeff_one]
  split_ifs
  · exact intC_one
  · exact intC_zero

theorem intS_pow {f : MvPowerSeries σ C} (hf : IntS v f) (n : ℕ) : IntS v (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact intS_one
  | succ n ih =>
    rw [pow_succ]
    exact intS_mul ih hf

theorem intS_prod {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS v (f i)) :
    IntS v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntS v) (fun _ _ => intS_mul) intS_one h

private theorem hasSubst_lemma [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

theorem intS_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS v (a s)) {γ : MvPowerSeries σ C} (hγ : IntS v γ) : IntS v (subst a γ) := by
  have hsub : HasSubst a := hasSubst_lemma ha0
  intro μ
  rw [coeff_subst hsub]
  refine intC_finsum fun d => ?_
  rw [smul_eq_mul]
  exact intC_mul (hγ d) (intS_prod _ (fun s _ => intS_pow (ha s) _) μ)

def LowLt {σ : Type*} (K : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < K → IntC v (coeff μ f)

def OrdV {σ : Type*} (D : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < D → coeff μ f = 0

private theorem degree_add_lemma_2 (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add _ a b
  | exact Finsupp.sum_add_index' (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

theorem low_mul {E D D' : ℕ} {f g : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f)
    (hg : OrdV D' g) (hg' : LowLt (v := v) (E + D') g) :
    OrdV (D + D') (f * g) ∧ LowLt (v := v) (E + (D + D')) (f * g) := by
  constructor
  · intro μ hμ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
    · rw [hg p.2 (by omega), mul_zero]
  · intro μ hμ
    rw [coeff_mul]
    refine intC_sum _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
      exact intC_zero
    · by_cases h2 : p.2.degree < D'
      · rw [hg p.2 h2, mul_zero]
        exact intC_zero
      · exact intC_mul (hf' p.1 (by omega)) (hg' p.2 (by omega))

theorem low_one (E : ℕ) : OrdV 0 (1 : MvPowerSeries σ C) ∧ LowLt (v := v) E (1 : MvPowerSeries σ C) :=
  ⟨fun _ hμ => absurd hμ (Nat.not_lt_zero _), fun μ _ => intS_one μ⟩

theorem low_pow {E D : ℕ} {f : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f) (n : ℕ) :
    OrdV (n * D) (f ^ n) ∧ LowLt (v := v) (E + n * D) (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.add_zero]
    exact low_one E
  | succ n ih =>
    rw [pow_succ, Nat.add_mul, Nat.one_mul]
    exact low_mul ih.1 ih.2 hf hf'

theorem low_prod {E : ℕ} {t : σ → MvPowerSeries σ C} (ht : ∀ s, OrdV 1 (t s))
    (ht' : ∀ s, LowLt (v := v) (E + 1) (t s)) (S : Finset σ) (d : σ → ℕ) :
    OrdV (∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) ∧ LowLt (v := v) (E + ∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, Nat.add_zero]
    exact low_one E
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp := low_pow (ht a) (ht' a) (d a)
    rw [Nat.mul_one] at hp
    exact low_mul hp.1 hp.2 ih.1 ih.2

theorem deg_one_single (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ y, d = Finsupp.single y 1 := by
  have hdeg : ∑ i ∈ d.support, d i = 1 := h
  have h1 : ∀ x ∈ d.support, d x = 1 := by
    intro x hx
    have hle := Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) hx
    have h0 : d x ≠ 0 := Finsupp.mem_support_iff.1 hx
    omega
  have hcard : d.support.card = 1 := by
    rw [← hdeg, Finset.sum_congr rfl h1]
    simp
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcard
  refine ⟨y, Finsupp.ext fun x => ?_⟩
  by_cases hx : x = y
  · subst hx
    rw [Finsupp.single_eq_same]
    exact h1 x (by rw [hy]; exact Finset.mem_singleton_self x)
  · have hxs : x ∉ d.support := by
      rw [hy]
      simpa using hx
    have hdx : d x = 0 := by
      by_contra h'
      exact hxs (Finsupp.mem_support_iff.2 h')
    rw [hdx, Finsupp.single_apply, if_neg (Ne.symm hx)]

theorem intC_det {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n C) (hA : ∀ i j, IntC v (A i j)) :
    IntC v A.det := by
  rw [Matrix.det_apply]
  refine intC_sum _ fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact intC_mul (intC_intCast _) (intC_prod _ fun i _ => hA _ _)

theorem intS_inv [Fintype σ] (Φ t : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x) : ∀ y, IntS v (t y) := by
  obtain ⟨L, hLdef⟩ : ∃ L : Matrix σ σ C, L = Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) :=
    ⟨_, rfl⟩
  rw [← hLdef] at hL
  have hts : HasSubst t := hasSubst_lemma ht0
  have hLent : ∀ k l, IntC v (L k l) := by
    intro k l
    rw [hLdef, Matrix.of_apply]
    exact hΦ k _
  have hdeg0 : ∀ d : σ →₀ ℕ, d.degree = 0 → d = 0 := by
    intro d hd
    have h0 : ∑ i ∈ d.support, d i = 0 := hd
    rw [Finset.sum_eq_zero_iff] at h0
    ext i
    by_contra hi
    exact hi (h0 i (Finsupp.mem_support_iff.2 hi))
  have hord : ∀ y, OrdV 1 (t y) := by
    intro y μ hμ
    rw [hdeg0 μ (by omega), coeff_zero_eq_constantCoeff_apply, ht0]
  have hdet0 : L.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hL
    simp at hL
  have hinv : IntC v (L.det)⁻¹ := by
    have h1 : v (L.det * (L.det)⁻¹) = 0 := by rw [mul_inv_cancel₀ hdet0, AddValuation.map_one]
    rw [AddValuation.map_mul, hL, zero_add] at h1
    exact le_of_eq h1.symm
  have hadj : ∀ a b, IntC v (L.adjugate a b) := by
    intro a b
    rw [Matrix.adjugate_apply]
    refine intC_det _ fun k l => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact intC_one
      · exact intC_zero
    · exact hLent k l
  have hNint : ∀ x, IntS v (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
    intro x d
    rw [map_sub, map_sum]
    refine intC_sub (hΦ x d) (intC_sum _ fun y _ => ?_)
    rw [coeff_smul, coeff_X]
    split_ifs
    · rw [mul_one]
      exact hLent x y
    · rw [mul_zero]
      exact intC_zero
  have hNlow : ∀ x, OrdV 2 (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
    intro x d hd
    by_cases h1 : d.degree = 1
    · obtain ⟨z, rfl⟩ := deg_one_single d h1
      rw [map_sub, map_sum]
      have hs : ∀ y, coeff (Finsupp.single z 1) (L x y • (X y : MvPowerSeries σ C)) =
          if y = z then L x y else 0 := by
        intro y
        rw [coeff_smul, coeff_X]
        by_cases hyz : y = z
        · subst hyz
          simp
        · rw [if_neg hyz, if_neg, mul_zero]
          intro h
          exact hyz ((Finsupp.single_left_inj one_ne_zero).1 h).symm
      rw [Finset.sum_congr rfl fun y _ => hs y, Finset.sum_ite_eq' Finset.univ z, if_pos (Finset.mem_univ z),
        hLdef, Matrix.of_apply, sub_self]
    · have hd0 := hdeg0 d (by omega)
      subst hd0
      rw [map_sub, map_sum]
      simp only [coeff_smul, coeff_zero_X, mul_zero, Finset.sum_const_zero, sub_zero]
      rw [coeff_zero_eq_constantCoeff_apply, hΦ0]
  have hsplit : ∀ x, (X x : MvPowerSeries σ C) =
      (∑ y, L x y • t y) + subst t (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
    intro x
    have e1 : subst t (Φ x) = subst t (∑ y, L x y • (X y : MvPowerSeries σ C)) +
        subst t (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
      conv_lhs => rw [show Φ x = (∑ y, L x y • (X y : MvPowerSeries σ C)) +
        (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) by ring]
      rw [← coe_substAlgHom hts, map_add]
    have e2 : subst t (∑ y, L x y • (X y : MvPowerSeries σ C)) = ∑ y, L x y • t y := by
      rw [← coe_substAlgHom hts, map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_smul, coe_substAlgHom, subst_X hts]
    rw [← heq x, e1, e2]
  have hlow : ∀ K, ∀ y, LowLt (v := v) K (t y) := by
    intro K
    induction K with
    | zero =>
      intro y μ hμ
      exact absurd hμ (Nat.not_lt_zero _)
    | succ K ih =>
      intro y μ hμ
      by_cases hlt : μ.degree < K
      · exact ih y μ hlt
      have hμK : μ.degree = K := by omega
      by_cases hK0 : K = 0
      · rw [hord y μ (by omega)]
        exact intC_zero
      have ih' : ∀ s, LowLt (v := v) (K - 1 + 1) (t s) := by
        intro s
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hK0)]
        exact ih s
      have hLw : ∀ x, IntC v ((Matrix.mulVec L fun y => coeff μ (t y)) x) := by
        intro x
        have hc := congrArg (coeff μ) (hsplit x)
        rw [map_add, map_sum] at hc
        simp only [coeff_smul] at hc
        have hmv : (Matrix.mulVec L fun y => coeff μ (t y)) x = ∑ y, L x y * coeff μ (t y) := rfl
        have hval : (Matrix.mulVec L fun y => coeff μ (t y)) x = coeff μ (X x : MvPowerSeries σ C) -
            coeff μ (subst t (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C))) := by
          rw [hmv, hc]
          ring
        rw [hval]
        refine intC_sub ?_ ?_
        · rw [coeff_X]
          split_ifs
          · exact intC_one
          · exact intC_zero
        · rw [coeff_subst hts]
          refine intC_finsum fun d => ?_
          rw [smul_eq_mul]
          by_cases hd : d.degree < 2
          · rw [hNlow x d hd, zero_mul]
            exact intC_zero
          · have hdd : d.degree = ∑ s ∈ d.support, d s := rfl
            have hP := (low_prod hord ih' d.support d).2 μ (by omega)
            exact intC_mul (hNint x d) hP
      have hdw : (Matrix.mulVec L.adjugate (Matrix.mulVec L fun y => coeff μ (t y))) y = L.det * coeff μ (t y) := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
        first
        | (rw [Matrix.smul_mulVec, Matrix.one_mulVec]; rfl)
        | simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
        | simp [Matrix.mulVec, Matrix.dotProduct, Matrix.one_apply]
      have hw : coeff μ (t y) = (L.det)⁻¹ * (Matrix.mulVec L.adjugate (Matrix.mulVec L fun y => coeff μ (t y))) y := by
        rw [hdw, inv_mul_cancel_left₀ hdet0]
      rw [hw]
      exact intC_mul hinv (intC_sum _ fun z _ => intC_mul (hadj _ _) (hLw z))
  intro y μ
  exact hlow (μ.degree + 1) y μ (Nat.lt_succ_self _)

theorem image_eq_int [Fintype σ] (Φ t : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t γ} = {F | IntS v F} := by
  have htI : ∀ y, IntS v (t y) := intS_inv Φ t hΦ0 hΦ hL ht0 heq
  ext F
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact intS_subst ht0 htI hγ
  · intro hF
    have hΦs : HasSubst Φ := hasSubst_lemma hΦ0
    have hts : HasSubst t := hasSubst_lemma ht0
    refine ⟨subst Φ F, intS_subst hΦ0 hΦ hF, ?_⟩
    rw [subst_comp_subst_apply hΦs hts]
    have hX : (fun x => subst t (Φ x)) = (X : σ → MvPowerSeries σ C) := funext heq
    rw [hX, subst_self]
    rfl

theorem image_eq_image [Fintype σ] (Φ t Φ₂ t₂ : σ → MvPowerSeries σ C)
    (hΦ0 : ∀ x, constantCoeff (Φ x) = 0) (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x)
    (hΦ0₂ : ∀ x, constantCoeff (Φ₂ x) = 0) (hΦ₂ : ∀ x, IntS v (Φ₂ x))
    (hL₂ : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ₂ x)).det = 0)
    (ht0₂ : ∀ y, constantCoeff (t₂ y) = 0) (heq₂ : ∀ x, subst t₂ (Φ₂ x) = X x) :
    {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t γ} =
      {F : MvPowerSeries σ C | ∃ γ, IntS v γ ∧ F = subst t₂ γ} := by
  rw [image_eq_int Φ t hΦ0 hΦ hL ht0 heq, image_eq_int Φ₂ t₂ hΦ0₂ hΦ₂ hL₂ ht0₂ heq₂]

end Formalism.L2.FormalSeriesBounds.AltInv
