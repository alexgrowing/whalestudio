import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem approxB_jForm_add_right (p : ℕ) {r : ℕ} (x y z : Fin r → ℂ) :
    jForm p x (y + z) = jForm p x y + jForm p x z := by
  simp only [jForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem approxB_jForm_smul_right (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p x (a • y) = a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem approxB_jForm_sub_right (p : ℕ) {r : ℕ} (x y z : Fin r → ℂ) :
    jForm p x (y - z) = jForm p x y - jForm p x z := by
  simp only [jForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem approxB_jForm_sum_right (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (x : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p x (∑ j ∈ s, f j) = ∑ j ∈ s, jForm p x (f j) := by
  simp only [jForm, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem approxB_jForm_smul_left (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p (a • x) y = conj a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem approxB_jForm_sum_left (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (y : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  simp only [jForm, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem approxB_jForm_conj (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : conj (jForm p x y) = jForm p y x := by
  rw [jForm, jForm, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (k : ℕ) < p <;> simp [sgn, h, mul_comm]

theorem approxB_posSq_nonneg (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity

theorem approxB_negSq_nonneg (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity

theorem approxB_normSq_nonneg {r : ℕ} (u : Fin r → ℂ) : 0 ≤ normSq u := Finset.sum_nonneg fun k _ => by positivity

theorem approxB_posSq_add_negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    posSq p u + negSq p u = normSq u := by
  rw [posSq, negSq, normSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

theorem approxB_jForm_self (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    jForm p u u = ((posSq p u - negSq p u : ℝ) : ℂ) := by
  rw [jForm, posSq, negSq, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  by_cases h : (k : ℕ) < p <;> simp [sgn, h]

theorem approxB_jForm_self_re (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    (jForm p u u).re = posSq p u - negSq p u := by
  rw [approxB_jForm_self, Complex.ofReal_re]

theorem approxB_norm_jForm_self_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖jForm p u u‖ ≤ normSq u := by
  rw [approxB_jForm_self, Complex.norm_real, Real.norm_eq_abs, ← approxB_posSq_add_negSq]
  have h1 := approxB_posSq_nonneg p u
  have h2 := approxB_negSq_nonneg p u
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem approxB_normSq_add_le {r : ℕ} (a b : Fin r → ℂ) :
    normSq (a + b) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply]
  have h1 : ‖a k + b k‖ ^ 2 ≤ (‖a k‖ + ‖b k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]

theorem approxB_normSq_single {r : ℕ} (j : Fin r) (R : ℝ) :
    normSq ((R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) = R ^ 2 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp [sq_abs]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

abbrev ApproxPosIdx (r p : ℕ) := {j : Fin r // (j : ℕ) < p}

theorem approxB_sum_pos {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, ¬ (j : ℕ) < p → f j = 0) : ∑ j, f j = ∑ k : ApproxPosIdx r p, f k := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun j : Fin r => (j : ℕ) < p))
    (fun j _ hj => hf j (by simpa using hj))]
  exact Finset.sum_subtype _ (fun j => by simp) f

theorem approxB_sum_neg {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, (j : ℕ) < p → f j = 0) :
    ∑ j, f j = ∑ k : {j : Fin r // ¬ (j : ℕ) < p}, f k := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun j : Fin r => ¬ (j : ℕ) < p))
    (fun j _ hj => hf j (by simpa using hj))]
  exact Finset.sum_subtype _ (fun j => by simp) f

theorem approxB_card_pos {r p : ℕ} (hp : p ≤ r) : Fintype.card (ApproxPosIdx r p) = p := by
  let e : ApproxPosIdx r p ≃ Fin p :=
    { toFun := fun j => ⟨j.1, j.2⟩
      invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hp⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem approxB_card_neg {r p : ℕ} (hp : p ≤ r) :
    Fintype.card {j : Fin r // ¬ (j : ℕ) < p} = r - p := by
  rw [Fintype.card_subtype_compl, approxB_card_pos hp, Fintype.card_fin]

def approxPadPos {r p : ℕ} (x : ApproxPosIdx r p → ℂ) : Fin r → ℂ :=
  fun j => if h : (j : ℕ) < p then x ⟨j, h⟩ else 0

theorem approxB_pad_sum {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (X : Fin r → Fin r → ℂ) :
    ∑ j, approxPadPos x j • X j = ∑ k : ApproxPosIdx r p, x k • X k.1 := by
  rw [approxB_sum_pos (p := p) _ (fun j hj => by simp [approxPadPos, hj])]
  exact Finset.sum_congr rfl fun k _ => by simp [approxPadPos, k.2]

theorem approxB_pad_ne {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (hx : x ≠ 0) : approxPadPos x ≠ 0 := by
  intro h
  apply hx
  funext k
  have h1 := congr_fun h k.1
  simpa [approxPadPos, k.2] using h1

theorem approxB_pad_zero {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (j : Fin r) (hj : p ≤ (j : ℕ)) :
    approxPadPos x j = 0 := by
  simp [approxPadPos, not_lt.mpr hj]

theorem approxB_graph_pos {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)))
    (x : ApproxPosIdx r p → ℂ) :
    0 ≤ (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re ∧
    (x ≠ 0 → 0 < (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re) := by
  obtain ⟨h1, h2⟩ := hg (approxPadPos x) (fun j hj => approxB_pad_zero x j hj)
  rw [approxB_pad_sum] at h1 h2
  rw [approxB_jForm_self_re]
  have hρ' : (ρ / 3) ^ 2 ≤ 1 / 9 := by
    have h3 : ρ / 3 ≤ 1 / 3 := by linarith
    have h4 : 0 ≤ ρ / 3 := by linarith
    nlinarith
  have hp0 := approxB_posSq_nonneg p (∑ k, x k • X k.1)
  refine ⟨by nlinarith, fun hx => ?_⟩
  have h5 := h2 (approxB_pad_ne x hx)
  nlinarith

theorem approxB_gram_posSemidef {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) :
    (Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext k j
    simp [Matrix.conjTranspose_apply, approxB_jForm_conj]
  · have e : star x ⬝ᵥ ((Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)) *ᵥ x) =
        jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1) := by
      rw [approxB_jForm_sum_left]
      simp only [approxB_jForm_smul_left, approxB_jForm_sum_right, approxB_jForm_smul_right]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
        Complex.star_def]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, approxB_jForm_self]
    have h := (approxB_graph_pos hρ1 hρ X hg x).1
    rw [approxB_jForm_self_re] at h
    exact Complex.zero_le_real.mpr (by linarith)

theorem approxB_det_le_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (hN : N.PosSemidef)
    (c : ℝ) (hc : ∀ k, (N k k).re ≤ c) : ‖N.det‖ ≤ c ^ Fintype.card n := by
  classical
  have hH := hN.isHermitian
  have hdet : N.det = ∏ i, (hH.eigenvalues i : ℂ) := hH.det_eq_prod_eigenvalues
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hN.eigenvalues_nonneg
  have htr : ∑ i, hH.eigenvalues i = ∑ k, (N k k).re := by
    have h2 := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hnorm : ‖N.det‖ = ∏ i, hH.eigenvalues i := by
    rw [hdet, norm_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hl i)]
  rw [hnorm]
  have hsum : ∑ i, hH.eigenvalues i ≤ Fintype.card n * c := by
    rw [htr]
    calc ∑ k, (N k k).re ≤ ∑ _k : n, c := Finset.sum_le_sum fun k _ => hc k
      _ = Fintype.card n * c := by simp
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    simp [h0]
  · have hm : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    have hAM := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / Fintype.card n)
      hH.eigenvalues (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp) (fun i _ => hl i)
    have h2 : ∑ i, (1 : ℝ) / Fintype.card n * hH.eigenvalues i ≤ c := by
      rw [← Finset.mul_sum, div_mul_eq_mul_div, one_mul, div_le_iff₀ hm]
      linarith
    have hG : 0 ≤ ∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hl i) _
    calc ∏ i, hH.eigenvalues i = (∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n)) ^ Fintype.card n := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hl i), one_div_mul_cancel hm.ne', Real.rpow_one]
      _ ≤ c ^ Fintype.card n := pow_le_pow_left₀ hG (hAM.trans h2) _

end ReciprocityTheory.MultiplicativeHeights
