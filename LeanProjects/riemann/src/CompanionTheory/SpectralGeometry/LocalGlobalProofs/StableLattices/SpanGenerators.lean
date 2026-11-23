import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartan

open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu GlobalTheory.CompanionTheory.BmuDecomp

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuSpan

section general

variable {n : ℕ}

theorem lie_conj {A B P Q X : Matrix (Fin n) (Fin n) ℂ} (hQ : Qᴴ * B * Q = A) (hQP : Q * P = 1)
    (hX : Lie B X) : Lie A (P * X * Q) := by
  unfold Lie at *
  have h1 : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Pᴴ * (Qᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Q * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have : (P * X * Q)ᴴ * A + A * (P * X * Q) = Qᴴ * (Xᴴ * B + B * X) * Q := by
    rw [← hQ]
    simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, c1, c2]
  rw [this, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem lie_sub {A X Y : Matrix (Fin n) (Fin n) ℂ} (hX : Lie A X) (hY : Lie A Y) : Lie A (X - Y) := by
  unfold Lie at *
  have : (X - Y)ᴴ * A + A * (X - Y) = (Xᴴ * A + A * X) - (Yᴴ * A + A * Y) := by
    rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [this, hX, hY, sub_zero]

theorem lie_add {A X Y : Matrix (Fin n) (Fin n) ℂ} (hX : Lie A X) (hY : Lie A Y) : Lie A (X + Y) := by
  unfold Lie at *
  have : (X + Y)ᴴ * A + A * (X + Y) = (Xᴴ * A + A * X) + (Yᴴ * A + A * Y) := by
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
  rw [this, hX, hY, add_zero]

end general

variable {k r : ℕ}

def pr (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if outer k r i then ⟨2 * r + k - i.val, by omega⟩ else i

theorem pr_val (i : Fin (2 * r + k + 1)) :
    (pr k r i).val = if i.val ≤ r ∨ r + k ≤ i.val then 2 * r + k - i.val else i.val := by
  unfold pr
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem pr_pr (i : Fin (2 * r + k + 1)) : pr k r (pr k r i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [pr_val]
  split_ifs <;> omega

theorem hq_apply (i j : Fin (2 * r + k + 1)) : Hq k r i j = if j = pr k r i then 1 else 0 := by
  have := i.isLt
  simp only [Hq, outer, Fin.ext_iff, pr_val]
  split_ifs <;> first | omega | rfl

theorem hq_apply' (i j : Fin (2 * r + k + 1)) : Hq k r i j = if i = pr k r j then 1 else 0 := by
  rw [hq_apply]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · rw [h, pr_pr]
  · rw [h, pr_pr]

theorem lie_hq_iff (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Lie (Hq k r) X ↔ ∀ i j, star (X (pr k r j) i) + X (pr k r i) j = 0 := by
  have h : ∀ i j, (Xᴴ * Hq k r + Hq k r * X) i j = star (X (pr k r j) i) + X (pr k r i) j := by
    intro i j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    congr 1
    · simp [hq_apply' _ j, conjTranspose_apply]
    · simp [hq_apply i]
  unfold Lie
  rw [← Matrix.ext_iff]
  simp only [h, Matrix.zero_apply]

def mask {n : ℕ} (p : Fin n → Fin n → Prop) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => by classical exact if p i j then X i j else 0

theorem mask_pos {n : ℕ} {p : Fin n → Fin n → Prop} {X : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (h : p i j) :
    mask p X i j = X i j := if_pos h

theorem mask_neg {n : ℕ} {p : Fin n → Fin n → Prop} {X : Matrix (Fin n) (Fin n) ℂ} {i j : Fin n} (h : ¬ p i j) :
    mask p X i j = 0 := if_neg h

theorem lie_mask {p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Prop}
    (hp : ∀ i j, p (pr k r j) i → p (pr k r i) j) {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Lie (Hq k r) X) : Lie (Hq k r) (mask p X) := by
  rw [lie_hq_iff] at *
  intro i j
  by_cases h : p (pr k r j) i
  · rw [mask_pos h, mask_pos (hp i j h), hX]
  · rw [mask_neg h, mask_neg (fun h' => h (hp j i h'))]; simp

theorem lie_swap {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Lie (Hq k r) X) : Lie (Hq k r) (X.submatrix (pr k r) (pr k r)) := by
  rw [lie_hq_iff] at *
  intro i j
  exact hX (pr k r i) (pr k r j)

theorem lie_scalar {a : ℂ} (ha : star a + a = 0) : Lie (Hq k r) (a • (1 : Matrix (Fin (2 * r + k + 1)) _ ℂ)) := by
  unfold Lie
  rw [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    ← add_smul, ha, zero_smul]

def blk (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Prop :=
  (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)

theorem up_pr (i j : Fin (2 * r + k + 1)) (h : up k r (pr k r j) i) : up k r (pr k r i) j := by
  have := i.isLt
  have := j.isLt
  simp only [up, outer, Fin.lt_def, pr_val] at *
  split_ifs at * <;> omega

theorem blk_pr (i j : Fin (2 * r + k + 1)) : blk k r (pr k r j) i ↔ blk k r (pr k r i) j := by
  have := i.isLt
  have := j.isLt
  simp only [blk, pr_val] at *
  split_ifs at * <;> omega

theorem span_hq (hk : 1 ≤ k) {Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hY : Lie (Hq k r) Y) :
    ∃ B A C : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Lie (Hq k r) B ∧ Lie (Hq k r) A ∧ Lie (Hq k r) C ∧ (∀ i j, ¬ blk k r i j → B i j = 0) ∧
      (∀ i, B i (wI k r 0) = B i (wI k r (Fin.last k))) ∧
      (∀ i j, ¬ (up k r i j ∧ ¬ blk k r i j) → A i j = 0) ∧ (∀ i j, up k r i j → C i j = 0) ∧ Y = B + A + C := by
  have p0 : pr k r (wI k r 0) = wI k r (Fin.last k) := by
    apply Fin.ext; simp [pr_val, wI]; omega
  have p1 : pr k r (wI k r (Fin.last k)) = wI k r 0 := by rw [← p0, pr_pr]
  set a := Y (wI k r 0) (wI k r (Fin.last k)) with ha
  have ha' : star a + a = 0 := by
    have := (lie_hq_iff Y).1 hY (wI k r (Fin.last k)) (wI k r (Fin.last k))
    rwa [p1] at this
  set U := mask (up k r) Y with hU
  have lU : Lie (Hq k r) U := lie_mask up_pr hY
  set B := mask (blk k r) (U + U.submatrix (pr k r) (pr k r) + a • 1) with hB
  have lB : Lie (Hq k r) B :=
    lie_mask (fun i j => (blk_pr i j).1) (lie_add (lie_add lU (lie_swap lU)) (lie_scalar ha'))
  set A := mask (fun i j => up k r i j ∧ ¬ blk k r i j) Y with hA
  have lA : Lie (Hq k r) A :=
    lie_mask (fun i j h => ⟨up_pr i j h.1, fun h' => h.2 ((blk_pr i j).2 h')⟩) hY
  refine ⟨B, A, Y - B - A, lB, lA, lie_sub (lie_sub hY lB) lA, fun i j h => mask_neg h, fun i => ?_,
    fun i j h => mask_neg h, fun i j h => ?_, by abel⟩
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have b0 : blk k r i (wI k r 0) := ⟨hi, by simp [wI]⟩
      have b1 : blk k r i (wI k r (Fin.last k)) := ⟨hi, by simp [wI]⟩
      have u0 : ∀ l : Fin (2 * r + k + 1), r ≤ l.val → U l (wI k r 0) = 0 := fun l hl =>
        mask_neg (by simp only [up, wI, Fin.lt_def, Fin.val_zero]; omega)
      have hpi : r ≤ (pr k r i).val := by rw [pr_val]; split_ifs <;> omega
      have ud : U (wI k r (Fin.last k)) (wI k r (Fin.last k)) = 0 := mask_neg (by simp [up])
      have ua : U (wI k r 0) (wI k r (Fin.last k)) = a :=
        mask_pos (by simp only [up, outer, wI, Fin.lt_def, Fin.val_zero, Fin.val_last]; omega)
      have hne : wI k r 0 ≠ wI k r (Fin.last k) := by
        simp only [wI, Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
      rw [hB, mask_pos b0, mask_pos b1]
      simp only [Matrix.add_apply, submatrix_apply, p0, p1, u0 i hi.1, u0 _ hpi, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      by_cases h0 : i = wI k r 0
      · rw [h0, p0, ud, ua]; simp [hne]
      · by_cases h1 : i = wI k r (Fin.last k)
        · rw [h1, p1, ud, ua]; simp [hne.symm]
        · have : pr k r i = i := by
            apply Fin.ext
            simp only [wI, Fin.ext_iff, Fin.val_zero, Fin.val_last] at h0 h1
            rw [pr_val, if_neg (by omega)]
          rw [this]; simp [h0, h1]
    · rw [hB, mask_neg (fun h => hi h.1), mask_neg (fun h => hi h.1)]
  · rw [Matrix.sub_apply, Matrix.sub_apply]
    by_cases hb : blk k r i j
    · have h2 : ¬ up k r (pr k r i) (pr k r j) := by
        simp only [up, blk, outer, Fin.lt_def, pr_val] at *
        split_ifs at * <;> omega
      rw [hA, mask_neg (fun h' => h'.2 hb), hB, mask_pos hb]
      simp only [Matrix.add_apply, submatrix_apply, Matrix.smul_apply, hU, mask_pos h, mask_neg h2,
        Matrix.one_apply_ne (ne_of_lt h.1)]
      simp
    · rw [hA, mask_pos ⟨h, hb⟩, hB, mask_neg hb]; simp

theorem spanG : SpanG := by
  intro k r z P hk hΓ Y hY
  obtain ⟨hP, hf, ρ, -, hz⟩ := hΓ
  obtain ⟨Q, hPQ, hQP⟩ := iso_exists_inv hP hq_sq
  have hQ := iso_inv hP hPQ
  have hinv : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  have bP := block_of_fix hP (fun a => ⟨hpk_e a, hpk_es a⟩) (fun a => ⟨hq_e a, hq_es a⟩) hf
  have bQ := block_of_fix hQ (fun a => ⟨hq_e a, hq_es a⟩) (fun a => ⟨hpk_e a, hpk_es a⟩)
    (fun a => ⟨fix_inv hQP (hf a).1, fix_inv hQP (hf a).2⟩)
  obtain ⟨B, A, C, lB, lA, lC, hB, hB0, hA, hC, e⟩ := span_hq hk (lie_conj hP hPQ hY)
  have col : ∀ j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → B *ᵥ bvec j = 0 := by
    intro j hj
    ext i
    simp only [bvec, mulVec_single_one, Matrix.col_apply, Pi.zero_apply]
    exact hB i j (fun h => by have := h.2; omega)
  have key : ∀ i j, (P * A * Q) i j = ∑ p, ∑ l, P i l * A l p * Q p j := by
    intro i j
    simp only [Matrix.mul_apply, Finset.sum_mul]
  refine ⟨P * B * Q, P * A * Q, P * C * Q, ⟨lie_conj hQ hQP lB, fun a => ⟨?_, ?_⟩, ?_⟩,
    ⟨lie_conj hQ hQP lA, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩, ⟨lie_conj hQ hQP lC, fun i j h => ?_⟩, ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, fix_inv hQP (hf a).1, col _ (Or.inl a.isLt), mulVec_zero]
  · rw [← mulVec_mulVec, ← mulVec_mulVec, fix_inv hQP (hf a).2,
      col _ (Or.inr (by have := a.isLt; simp only [esI]; omega)), mulVec_zero]
  · have : B *ᵥ (bvec (wI k r 0) - bvec (wI k r (Fin.last k))) = 0 := by
      ext i
      simp only [mulVec_sub, bvec, mulVec_single_one, Matrix.col_apply, Pi.zero_apply, Pi.sub_apply, hB0 i,
        sub_self]
    rw [hz, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, hQP, Matrix.mul_one, ← mulVec_mulVec, this,
      mulVec_zero, smul_zero]
  · rw [key]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun l _ => ?_
    have ha := a.isLt
    by_cases hp : p = eI k r a
    · subst hp
      by_cases hl : a.val ≤ l.val
      · rw [hA l _ (fun h => by have := h.1.1; simp only [eI, Fin.lt_def] at this; omega)]; simp
      · have : i ≠ l := by rintro rfl; exact hl hi
        rw [(bP l (Or.inl (by omega)) i).1, if_neg this]; simp
    · rw [(bQ (eI k r a) (Or.inl ha) p).1, if_neg hp]; simp
  · rw [key]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hp : p.val < r ∨ r + k < p.val
    · have : j ≠ p := by rintro rfl; omega
      rw [(bQ p hp j).2, if_neg this]; simp
    · by_cases hl : r ≤ l.val
      · rw [hA l p (fun h => h.2 (by have := h.1.1; simp only [blk, Fin.lt_def] at *; omega))]; simp
      · have : i ≠ l := by rintro rfl; exact hl hi
        rw [(bP l (Or.inl (by omega)) i).1, if_neg this]; simp
  · have : P⁻¹ * (P * C * Q) * P = C := by
      rw [hinv]
      simp only [← Matrix.mul_assoc]
      rw [hQP, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
    rw [this]
    exact hC i j h
  · rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, ← e]
    simp only [← Matrix.mul_assoc]
    rw [hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ, Matrix.mul_one]

end GlobalTheory.CompanionTheory.BmuSpan
