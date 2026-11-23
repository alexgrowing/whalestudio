import Formalism.HermitianCurvature.StatementU
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetNormLe

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux5

def EB {m n : Type*} (A : Matrix m n ℂ) (c : ℝ) : Prop := ∀ i j, ‖A i j‖ ≤ c

lemma EB.mono {m n : Type*} {A : Matrix m n ℂ} {a b : ℝ} (h : EB A a) (hab : a ≤ b) : EB A b :=
  fun i j => (h i j).trans hab

lemma EB_mul {l m n : Type*} [Fintype m] {A : Matrix l m ℂ} {B : Matrix m n ℂ} {a b : ℝ}
    (hA : EB A a) (hB : EB B b) : EB (A * B) (Fintype.card m * (a * b)) := by
  intro i k
  rw [mul_apply]
  calc ‖∑ j, A i j * B j k‖ ≤ ∑ j, ‖A i j * B j k‖ := norm_sum_le _ _
    _ ≤ ∑ _j : m, a * b := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hA i j) (hB j k) (norm_nonneg _) ((norm_nonneg _).trans (hA i j))
    _ = Fintype.card m * (a * b) := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma EB_conjTranspose {m n : Type*} {A : Matrix m n ℂ} {a : ℝ} (h : EB A a) : EB Aᴴ a := by
  intro i j
  simpa [conjTranspose_apply, norm_star] using h j i

lemma EB_add {m n : Type*} {A B : Matrix m n ℂ} {a b : ℝ} (hA : EB A a) (hB : EB B b) :
    EB (A + B) (a + b) :=
  fun i j => (norm_add_le _ _).trans (add_le_add (hA i j) (hB i j))

lemma EB_neg {m n : Type*} {A : Matrix m n ℂ} {a : ℝ} (h : EB A a) : EB (-A) a := by
  intro i j
  simpa using h i j

lemma EB_sub {m n : Type*} {A B : Matrix m n ℂ} {a b : ℝ} (hA : EB A a) (hB : EB B b) :
    EB (A - B) (a + b) := by
  rw [sub_eq_add_neg]
  exact EB_add hA (EB_neg hB)

lemma EB_one {n : Type*} [DecidableEq n] : EB (1 : Matrix n n ℂ) 1 := by
  intro i j
  rw [one_apply]
  split_ifs <;> simp

lemma EB_zero {m n : Type*} : EB (0 : Matrix m n ℂ) 0 := by
  intro i j
  simp

lemma EB_wMat (d : ℕ) : EB (G.wMat d) 1 := by
  intro i j
  simp only [G.wMat, of_apply]
  split_ifs <;> simp

lemma EB_Hpk (k r : ℕ) : EB (Hpk k r) 1 := by
  intro i j
  unfold Hpk
  split_ifs <;> simp

lemma mx_le {m n : Type*} [Fintype m] [Fintype n] {A : Matrix m n ℂ} {c : ℝ} (h : EB A c) (hc : 0 ≤ c) :
    mx A ≤ c := by
  unfold mx
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => ?_
  exact h i j

lemma entry_le_mx {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (i : m) (j : n) :
    ‖A i j‖ ≤ mx A := by
  unfold mx
  exact (norm_le_pi_norm (Matrix.of.symm A i) j).trans (norm_le_pi_norm (Matrix.of.symm A) i)

lemma det_norm_le {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {m : ℝ} (h : EB A m) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * m ^ Fintype.card n := by
  first | exact UpperTheory.Reformulated.B.Qi39.det_norm_le .. | (apply UpperTheory.Reformulated.B.Qi39.det_norm_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi39.det_norm_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi39.det_norm_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi39.det_norm_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi39.det_norm_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi39.det_norm_le n ‹_› ‹_› A m h | exact @UpperTheory.Reformulated.B.Qi39.det_norm_le n ‹_› ‹_› A m | exact @UpperTheory.Reformulated.B.Qi39.det_norm_le n ‹_› ‹_› A | exact @UpperTheory.Reformulated.B.Qi39.det_norm_le n ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qi39.det_norm_le n ‹_› | exact @UpperTheory.Reformulated.B.Qi39.det_norm_le n

lemma inv_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℝ} (h : EB A m) :
    EB A⁻¹ ((n - 1).factorial * m ^ (n - 1) / ‖A.det‖) := by
  intro i j
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Matrix.adjugate_fin_succ_eq_det_submatrix,
      norm_mul]
    have h1 : ‖((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ)))‖ = 1 := by simp
    rw [h1, one_mul]
    have h2 : ‖(A.submatrix j.succAbove i.succAbove).det‖ ≤ n.factorial * m ^ n := by
      have := det_norm_le (A.submatrix j.succAbove i.succAbove) (m := m) (fun a b => h _ _)
      simpa using this
    rw [Ring.inverse_eq_inv', norm_inv]
    simp only [Nat.add_sub_cancel]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (norm_nonneg _))

lemma pow_le_of_lb {m δ : ℝ} {e q : ℕ} (hm : 0 ≤ m) (hδ : 0 < δ) (hq : δ ≤ m ^ q) (he : e ≤ q) :
    m ^ e ≤ (1 + δ⁻¹) * m ^ q := by
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  rcases le_or_gt 1 m with h1 | h1
  · calc m ^ e ≤ m ^ q := pow_le_pow_right₀ h1 he
      _ ≤ (1 + δ⁻¹) * m ^ q := le_mul_of_one_le_left (by positivity) (by linarith)
  · calc m ^ e ≤ 1 := pow_le_one₀ hm h1.le
      _ = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
      _ ≤ δ⁻¹ * m ^ q := mul_le_mul_of_nonneg_left hq hi
      _ ≤ (1 + δ⁻¹) * m ^ q := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma self_le_pow_succ {m δ : ℝ} {q : ℕ} (hm : 0 ≤ m) (hδ : 0 < δ) (hq : δ ≤ m ^ q) :
    m ≤ (1 + δ⁻¹) * m ^ (q + 1) := by
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  rcases le_or_gt 1 m with h1 | h1
  · calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ (q + 1) := pow_le_pow_right₀ h1 (by omega)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith)
  · calc m = δ⁻¹ * (δ * m) := by field_simp
      _ ≤ δ⁻¹ * (m ^ q * m) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hm) hi
      _ = δ⁻¹ * m ^ (q + 1) := by rw [pow_succ]
      _ ≤ (1 + δ⁻¹) * m ^ (q + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma submatrix_mul_lower {p k : ℕ} (h : k ≤ p) (L X : Matrix (Fin p) (Fin p) ℂ)
    (hL : ∀ a b, a < b → L a b = 0) {l : Type*} (f : l → Fin p) :
    (L * X).submatrix (Fin.castLE h) f =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * X.submatrix (Fin.castLE h) f := by
  ext a b
  simp only [submatrix_apply, mul_apply]
  symm
  have e1 : ∑ t : Fin k, L (Fin.castLE h a) (Fin.castLE h t) * X (Fin.castLE h t) (f b) =
      ∑ t ∈ Finset.univ.map (Fin.castLEEmb h), L (Fin.castLE h a) t * X t (f b) := by
    rw [Finset.sum_map]
    rfl
  rw [e1]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro t _ ht
  have hk : k ≤ t.val := by
    by_contra hlt
    have hlt : t.val < k := not_le.mp hlt
    exact ht (Finset.mem_map.mpr ⟨⟨t.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hL _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega), zero_mul]

lemma ldu_upper_bound {p : ℕ} (L U : Matrix (Fin p) (Fin p) ℂ) (d : Fin p → ℂ)
    (hL : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1) (hU : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) {m : ℝ} (hM : EB (L * diagonal d * U) m) (i j' : Fin p) :
    ‖(∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)) * U i j'‖ ≤ (i.val + 1).factorial * m ^ (i.val + 1) := by
  set r : Fin (i.val + 1) → Fin p := Fin.castLE i.isLt with hr
  set f : Fin (i.val + 1) → Fin p := fun t => if t.val < i.val then r t else j' with hf
  have h1 : (L * diagonal d * U).submatrix r f = L.submatrix r r * (diagonal d * U).submatrix r f := by
    rw [mul_assoc]
    exact submatrix_mul_lower i.isLt L _ hL f
  have h2 : (L.submatrix r r).det = 1 := by
    have hb : (L.submatrix r r).BlockTriangular OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := hab
      simp only [submatrix_apply]
      apply hL
      rw [hr, Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]
      exact hab'
    rw [Matrix.det_of_isLowerTriangular _ hb]
    simp [hL1]
  have hrl : r (Fin.last i.val) = i := by
    apply Fin.ext
    simp [hr]
  have hfl : f (Fin.last i.val) = j' := by
    simp [hf]
  have hfc : ∀ t : Fin i.val, f t.castSucc = r t.castSucc := by
    intro t
    simp [hf, t.isLt]
  have h3 : ((diagonal d * U).submatrix r f).det = (∏ t, d (r t)) * U i j' := by
    have hb : ((diagonal d * U).submatrix r f).BlockTriangular id := by
      intro a b hab
      have hab' : b < a := hab
      simp only [submatrix_apply, diagonal_mul]
      have hb' : b.val < i.val := lt_of_lt_of_le hab' (Nat.lt_succ_iff.mp a.isLt)
      have : f b = r b := by simp [hf, hb']
      rw [this, hU _ _ (by rw [hr, Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]; exact hab'), mul_zero]
    rw [Matrix.det_of_isUpperTriangular hb, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [submatrix_apply, diagonal_mul, hfc, hrl, hfl, hU1, mul_one]
    ring
  have h4 := det_norm_le ((L * diagonal d * U).submatrix r f) (m := m) (fun a b => hM _ _)
  rw [h1, Matrix.det_mul, h2, h3, one_mul] at h4
  simpa using h4

lemma block2_mul {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' =
      blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blk2
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

lemma block2_one {p s : ℕ} : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  unfold blk2
  rw [fromBlocks_one, reindex_apply, submatrix_one_equiv]

lemma sizes_unipotent_first {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i j : Fin p) :
    blk2 A B C D (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = A i j := by
  simp [blk2]

lemma block2_apply_upper_right {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin p) (j : Fin s) :
    blk2 A B C D (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = B i j := by
  simp [blk2]

lemma sizes_unipotent_second {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) (j : Fin p) :
    blk2 A B C D (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = C i j := by
  simp [blk2]

lemma block2_apply_lower_right {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    blk2 A B C D (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = D i j := by
  simp [blk2]

lemma zj_affine {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (CC : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H CC = blk2 H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + CC) := by
  unfold Zj
  rw [block2_mul, block2_mul]
  simp

lemma det_upper' {p : ℕ} (u : G.UT p → ℂ) : (G.upper u).det = 1 := by
  have h : (G.upper u).BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    simp [G.upper, G.strictUpper, ne_of_gt hij, not_lt.mpr (le_of_lt hij)]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [G.upper, G.strictUpper]

lemma det_lowW' {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : (lowW σ v).det = 1 := by
  have h : (lowW σ v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have : ¬ (j < i ∧ σ.symm j < σ.symm i) := fun h => absurd h.1 (not_lt.mpr (le_of_lt hij'))
    simp [lowW, ne_of_lt hij', this]
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [lowW]

lemma permutationMatrix_eq_permMatrix {p : ℕ} (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by
  ext a b
  simp [wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma det_permutationMatrix_ne_zero {p : ℕ} (σ : Equiv.Perm (Fin p)) : (wP σ).det ≠ 0 := by
  rw [permutationMatrix_eq_permMatrix, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma permutationMatrix_mul_apply {p : ℕ} (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (wP σ * M) a b = M (σ a) b := by
  simp [wP, mul_apply]

lemma lowW_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a b : Fin p) (h : a < b) : lowW σ v a b = 0 := by
  have : ¬ (b < a ∧ σ.symm b < σ.symm a) := fun h' => absurd h'.1 (not_lt.mpr (le_of_lt h))
  simp [lowW, ne_of_lt h, this]

lemma lowW_diag {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a : Fin p) : lowW σ v a a = 1 := by
  simp [lowW]

lemma lowW_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (q : LW σ) : lowW σ v q.1.1 q.1.2 = v q := by
  have h := q.2
  simp [lowW, ne_of_gt h.1, h]

lemma upper_upper {p : ℕ} (u : G.UT p → ℂ) (a b : Fin p) (h : b < a) : G.upper u a b = 0 := by
  simp [G.upper, G.strictUpper, ne_of_gt h, not_lt.mpr (le_of_lt h)]

lemma upper_diag {p : ℕ} (u : G.UT p → ℂ) (a : Fin p) : G.upper u a a = 1 := by
  simp [G.upper, G.strictUpper]

lemma upper_entry {p : ℕ} (u : G.UT p → ℂ) (q : G.UT p) : G.upper u q.1.1 q.1.2 = u q := by
  have h := q.2
  simp [G.upper, G.strictUpper, ne_of_lt h, h]

lemma nat_mul_factorial_bound (p : ℕ) {m x : ℝ} (_hm : 0 ≤ m) (hx : 0 < x) :
    (p : ℝ) * (m * ((p - 1).factorial * m ^ (p - 1) / x)) ≤ (p.factorial : ℝ) / x * m ^ p := by
  cases p with
  | zero => simp; positivity
  | succ q =>
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    apply le_of_eq
    field_simp

lemma norm_pi_pi_le {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖f i j‖ ≤ c) : ‖f‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => h i j

lemma upper_factor_bound {p : ℕ} (L U : Matrix (Fin p) (Fin p) ℂ) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (hL : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1) (hU : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 < δ) (hδm : δ ≤ m ^ p)
    (hM : EB (L * diagonal d * U) m) (i j' : Fin p) :
    ‖U i j'‖ ≤ (∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖) *
      ((1 + δ⁻¹) * m ^ p) := by
  have h1 := ldu_upper_bound L U d hL hL1 hU hU1 hM i j'
  have hP : 0 < ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ :=
    norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun t _ => hd _)
  rw [norm_mul] at h1
  have h2 : ‖U i j'‖ ≤ ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ *
      m ^ (i.val + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hP]
    linarith [mul_comm ‖U i j'‖ ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖]
  have h3 : m ^ (i.val + 1) ≤ (1 + δ⁻¹) * m ^ p := pow_le_of_lb hm hδ hδm i.isLt
  have h4 : ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ ≤
      ∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖ :=
    Finset.single_le_sum (f := fun i : Fin p =>
      ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  calc ‖U i j'‖ ≤ _ := h2
    _ ≤ _ := mul_le_mul h4 h3 (by positivity) (le_trans (by positivity) h4)

theorem _root_.Formalism.FourierDecayAlt.P.aux_statement_17 : BlockHeadSizes := by
  intro p s σ d hd
  set dH : ℂ := (wP σ).det * ∏ i, d i with hdH
  have hdH0 : dH ≠ 0 := mul_ne_zero (det_permutationMatrix_ne_zero σ) (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  have hdHpos : 0 < ‖dH‖ := norm_pos_iff.mpr hdH0
  have hdetH : ∀ v u, (headH σ d v u).det = dH := by
    intro v u
    unfold headH
    rw [det_mul, det_mul, det_mul, det_upper', det_lowW', det_diagonal]
    ring
  set δ0 : ℝ := ‖dH‖ / (p.factorial : ℝ) with hδ0
  have hδ0pos : 0 < δ0 := by positivity
  set Kd : ℝ := ∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖
    with hKd
  have hKd0 : 0 ≤ Kd := Finset.sum_nonneg fun _ _ => by positivity
  have hδi : 0 ≤ δ0⁻¹ := inv_nonneg.mpr hδ0pos.le
  refine ⟨Kd * (1 + δ0⁻¹) + (p.factorial : ℝ) / ‖dH‖ + (1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖),
    fun η Z => ?_⟩
  obtain ⟨⟨a, b⟩, ⟨v, u⟩⟩ := η
  set H := headH σ d v u with hH
  set m := mx (ZjH σ d ((a, b), (v, u)) Z) with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hZj : ZjH σ d ((a, b), (v, u)) Z =
      blk2 H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + Matrix.of Z) := by
    unfold ZjH
    exact zj_affine _ _ _ _
  have hent : ∀ x y, ‖ZjH σ d ((a, b), (v, u)) Z x y‖ ≤ m := fun x y => entry_le_mx _ x y
  have hHb : EB H m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
    rwa [hZj, sizes_unipotent_first] at this
  have hHBb : EB (H * Matrix.of b) m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
    rwa [hZj, block2_apply_upper_right] at this
  have hAHb : EB (Matrix.of a * H) m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))
    rwa [hZj, sizes_unipotent_second] at this
  have hBRb : EB (Matrix.of a * H * Matrix.of b + Matrix.of Z) m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
    rwa [hZj, block2_apply_lower_right] at this
  have hδm : δ0 ≤ m ^ p := by
    have h := det_norm_le H hHb
    rw [hdetH, Fintype.card_fin] at h
    rw [hδ0, div_le_iff₀ (by positivity)]
    linarith

  set M0 := lowW σ v * diagonal d * G.upper u with hM0
  have hHM : H = wP σ * M0 := by
    simp only [hH, hM0, headH, mul_assoc]
  have hM0b : EB M0 m := by
    intro i j
    have := hHb (σ.symm i) j
    rwa [hHM, permutationMatrix_mul_apply, Equiv.apply_symm_apply] at this
  have hu : ∀ q : G.UT p, ‖u q‖ ≤ Kd * ((1 + δ0⁻¹) * m ^ p) := by
    intro q
    rw [← upper_entry u q]
    exact upper_factor_bound (lowW σ v) (G.upper u) d hd (lowW_lower σ v) (lowW_diag σ v) (upper_upper u)
      (upper_diag u) hm0 hδ0pos hδm hM0b _ _
  have hv : ∀ q : LW σ, ‖v q‖ ≤ Kd * ((1 + δ0⁻¹) * m ^ p) := by
    intro q
    rw [← lowW_entry σ v q]
    have eT : (G.upper u)ᵀ * diagonal d * (lowW σ v)ᵀ = M0ᵀ := by
      rw [hM0, transpose_mul, transpose_mul, diagonal_transpose, mul_assoc]
    have hT : EB ((G.upper u)ᵀ * diagonal d * (lowW σ v)ᵀ) m := by
      intro i j
      rw [eT, transpose_apply]
      exact hM0b j i
    have := upper_factor_bound ((G.upper u)ᵀ) ((lowW σ v)ᵀ) d hd
      (fun a b h => by rw [transpose_apply]; exact upper_upper u b a h)
      (fun a => by rw [transpose_apply]; exact upper_diag u a)
      (fun a b h => by rw [transpose_apply]; exact lowW_lower σ v b a h)
      (fun a => by rw [transpose_apply]; exact lowW_diag σ v a) hm0 hδ0pos hδm hT q.1.2 q.1.1
    rwa [transpose_apply] at this

  have hHu : IsUnit H.det := by rw [hdetH]; exact isUnit_iff_ne_zero.mpr hdH0
  have hHi : EB H⁻¹ ((p - 1).factorial * m ^ (p - 1) / ‖dH‖) := by
    have := inv_entry_le H hHb
    rwa [hdetH] at this
  set bA : ℝ := (p.factorial : ℝ) / ‖dH‖ * m ^ p with hbA
  have hfa := nat_mul_factorial_bound p hm0 hdHpos
  have ha : EB (Matrix.of a) bA := by
    have h1 : Matrix.of a = Matrix.of a * H * H⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hHu, Matrix.mul_one]
    have h2 := EB_mul hAHb hHi
    rw [← h1, Fintype.card_fin] at h2
    exact h2.mono hfa
  have hb : EB (Matrix.of b) bA := by
    have h1 : Matrix.of b = H⁻¹ * (H * Matrix.of b) := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hHu, Matrix.one_mul]
    have h2 := EB_mul hHi hHBb
    rw [← h1, Fintype.card_fin] at h2
    exact h2.mono ((le_of_eq (by ring)).trans hfa)
  have hbA0 : 0 ≤ bA := by positivity
  have hZb : EB (Matrix.of Z) (m + p * (m * bA)) := by
    have h1 : Matrix.of Z = (Matrix.of a * H * Matrix.of b + Matrix.of Z) - Matrix.of a * H * Matrix.of b := by abel
    have h2 := EB_sub hBRb (EB_mul hAHb hb)
    rwa [← h1, Fintype.card_fin] at h2
  have hself := self_le_pow_succ hm0 hδ0pos hδm
  have hmp : 0 ≤ m ^ p := pow_nonneg hm0 p
  set C := Kd * (1 + δ0⁻¹) + (p.factorial : ℝ) / ‖dH‖ + (1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖)
    with hC
  have hC1 : Kd * (1 + δ0⁻¹) ≤ C := by
    have h1 : 0 ≤ (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) := by positivity
    have h2 : 0 ≤ (p.factorial : ℝ) / ‖dH‖ := by positivity
    rw [hC]; linarith
  have hC2 : (p.factorial : ℝ) / ‖dH‖ ≤ C := by
    rw [hC]; have : 0 ≤ (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) := by positivity
    have : 0 ≤ Kd * (1 + δ0⁻¹) := by positivity
    linarith
  have hC3 : (1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) ≤ C := by
    rw [hC]; have : 0 ≤ (p.factorial : ℝ) / ‖dH‖ := by positivity
    have : 0 ≤ Kd * (1 + δ0⁻¹) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show ‖a‖ ≤ C * m ^ p
    refine norm_pi_pi_le a (by positivity) fun i t => (ha i t).trans ?_
    rw [hbA]
    exact mul_le_mul_of_nonneg_right hC2 hmp
  · show ‖b‖ ≤ C * m ^ p
    refine norm_pi_pi_le b (by positivity) fun i t => (hb i t).trans ?_
    rw [hbA]
    exact mul_le_mul_of_nonneg_right hC2 hmp
  · show ‖v‖ ≤ C * m ^ p
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => (hv q).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC1 hmp
  · show ‖u‖ ≤ C * m ^ p
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => (hu q).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC1 hmp
  · show ‖Z‖ ≤ C * m ^ (p + 1)
    refine norm_pi_pi_le Z (by positivity) fun i t => (hZb i t).trans ?_
    have e : m + p * (m * bA) ≤ ((1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖)) * m ^ (p + 1) := by
      rw [hbA, add_mul, pow_succ]
      have : (p : ℝ) * (m * ((p.factorial : ℝ) / ‖dH‖ * m ^ p)) =
          (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) * (m ^ p * m) := by ring
      rw [this]
      rw [pow_succ] at hself
      linarith
    exact e.trans (mul_le_mul_of_nonneg_right hC3 (by positivity))
  ·
    intro hZ0
    have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ0
    have hinv : (ZjH σ d ((a, b), (v, u)) Z)⁻¹ =
        blk2 1 (-(Matrix.of b)) 0 1 * blk2 H⁻¹ 0 0 (Matrix.of Z)⁻¹ * blk2 1 0 (-(Matrix.of a)) 1 := by
      apply Matrix.inv_eq_left_inv
      have e1 : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 (-(Matrix.of a)) 1 * blk2 1 0 (Matrix.of a) 1 = 1 := by
        rw [block2_mul]; simp [block2_one]
      have e2 : blk2 H⁻¹ 0 0 (Matrix.of Z)⁻¹ * blk2 H 0 0 (Matrix.of Z) = 1 := by
        rw [block2_mul]; simp [nonsing_inv_mul _ hHu, nonsing_inv_mul _ hZu, block2_one]
      have e3 : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (-(Matrix.of b)) 0 1 * blk2 1 (Matrix.of b) 0 1 = 1 := by
        rw [block2_mul]; simp [block2_one]
      unfold ZjH Zj
      simp only [mul_assoc]
      rw [← mul_assoc (blk2 1 0 (-(Matrix.of a)) 1), e1, one_mul, ← mul_assoc (blk2 H⁻¹ 0 0 (Matrix.of Z)⁻¹), e2,
        one_mul, e3]
    refine mx_le (fun i t => ?_) (norm_nonneg _)
    have e := congrFun (congrFun hinv (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv (Sum.inr t))
    rw [block2_mul, block2_mul, block2_apply_lower_right] at e
    simp at e
    rw [← e]
    exact entry_le_mx _ _ _

lemma one_add_le_mul_one_add_pow {x c m : ℝ} {k : ℕ} (hc : 0 ≤ c) (hm : 0 ≤ m) (h : x ≤ c * m ^ k) :
    1 + x ≤ (1 + c) * (1 + m) ^ k := by
  have h1 : m ^ k ≤ (1 + m) ^ k := pow_le_pow_left₀ hm (by linarith) k
  have h2 : 1 ≤ (1 + m) ^ k := one_le_pow₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]

theorem _root_.Formalism.FourierDecayAlt.P.sizes_top_level : SizesTop := by
  intro p s σ d hd hs A' hA'
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p s σ d hd
  set Cp := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  set K : ℝ := (1 + Cp) ^ 5 with hK
  have hK0 : 0 < K := by positivity
  have hps1 : (1 : ℝ) ≤ ((p + s : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p + s)
  have hps : (0 : ℝ) < 5 * ((p + s : ℕ) : ℝ) := by positivity
  set e := A' / (5 * ((p + s : ℕ) : ℝ)) with he
  have he0 : 0 ≤ e := div_nonneg hA' hps.le
  refine ⟨K ^ e, fun η CC => ?_⟩
  set m := mx (ZjH σ d η CC) with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hC η CC
  have up : ∀ {x : ℝ} {k : ℕ}, x ≤ C * m ^ k → x ≤ Cp * m ^ k := fun hx =>
    hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hm0 _))
  set X := wtH η * (1 + ‖CC‖) with hX
  have hX1 : 1 ≤ X := by
    have a1 : 1 ≤ 1 + ‖η.1.1‖ := by linarith [norm_nonneg η.1.1]
    have a2 : 1 ≤ 1 + ‖η.1.2‖ := by linarith [norm_nonneg η.1.2]
    have a3 : 1 ≤ 1 + ‖η.2.1‖ := by linarith [norm_nonneg η.2.1]
    have a4 : 1 ≤ 1 + ‖η.2.2‖ := by linarith [norm_nonneg η.2.2]
    have a5 : 1 ≤ 1 + ‖CC‖ := by linarith [norm_nonneg CC]
    rw [hX]
    unfold wtH
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 a2) a3) a4) a5
    exact this
  have hXle : X ≤ K * (1 + m) ^ (5 * p + 1) := by
    rw [hX]
    unfold wtH
    calc (1 + ‖η.1.1‖) * (1 + ‖η.1.2‖) * (1 + ‖η.2.1‖) * (1 + ‖η.2.2‖) * (1 + ‖CC‖)
        ≤ ((1 + Cp) * (1 + m) ^ p) * ((1 + Cp) * (1 + m) ^ p) * ((1 + Cp) * (1 + m) ^ p) *
            ((1 + Cp) * (1 + m) ^ p) * ((1 + Cp) * (1 + m) ^ (p + 1)) := by
          gcongr
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h1)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h2)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h3)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h4)
          · exact one_add_le_mul_one_add_pow hCp0 hm0 (up h5)
      _ = K * (1 + m) ^ (5 * p + 1) := by rw [hK]; ring
  have hexp : ((5 * p + 1 : ℕ) : ℝ) * e ≤ A' := by
    rw [he, mul_div_assoc', div_le_iff₀ hps]
    have : ((5 * p + 1 : ℕ) : ℝ) ≤ 5 * ((p + s : ℕ) : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    nlinarith
  have hXe : X ^ e ≤ K ^ e * (1 + m) ^ A' := by
    calc X ^ e ≤ (K * (1 + m) ^ (5 * p + 1)) ^ e := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ X) hXle he0
      _ = K ^ e * ((1 + m) ^ (5 * p + 1)) ^ e := Real.mul_rpow hK0.le (by positivity)
      _ = K ^ e * (1 + m) ^ (((5 * p + 1 : ℕ) : ℝ) * e) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ K ^ e * (1 + m) ^ A' :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 1 + m) hexp)
            (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < X) e),
    inv_mul_le_iff₀ (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + m) A')]
  linarith [mul_comm ((1 + m) ^ A') (K ^ e)]

section three

variable {k j ρ : ℕ}

def q1 (k ρ : ℕ) {j : ℕ} (a : Fin j) : Ix k j ρ := Sum.inl (Sum.inl a)

def q2 (k j : ℕ) {ρ : ℕ} (i : Fin (2 * ρ + k + 1)) : Ix k j ρ := Sum.inl (Sum.inr i)

def q3 (k ρ : ℕ) {j : ℕ} (a : Fin j) : Ix k j ρ := Sum.inr a

def bk {ι κ : Type*} (M : B.Mat k (j + ρ)) (f : ι → Ix k j ρ) (f' : κ → Ix k j ρ) : Matrix ι κ ℂ :=
  Matrix.of fun a b => M (eB k j ρ (f a)) (eB k j ρ (f' b))

lemma aux_statement_16 (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin j) (Fin j) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A31 : Matrix (Fin j) (Fin j) ℂ)
    (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33
        x y := by
  simp [blk3]

lemma block3_mul_blocks (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin j) (Fin j) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A31 : Matrix (Fin j) (Fin j) ℂ)
    (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)
    (B13 : Matrix (Fin j) (Fin j) ℂ) (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ)
    (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B31 : Matrix (Fin j) (Fin j) ℂ)
    (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 * blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 * ToralGalois + A12 * B21 + A13 * B31) (A11 * cocyclesToWachVectorsExponent + A12 * B22 + A13 * B32)
        (A11 * B13 + A12 * B23 + A13 * B33) (A21 * ToralGalois + A22 * B21 + A23 * B31)
        (A21 * cocyclesToWachVectorsExponent + A22 * B22 + A23 * B32) (A21 * B13 + A22 * B23 + A23 * B33)
        (A31 * ToralGalois + A32 * B21 + A33 * B31) (A31 * cocyclesToWachVectorsExponent + A32 * B22 + A33 * B32)
        (A31 * B13 + A32 * B23 + A33 * B33) := by
  unfold blk3
  rw [reindex_apply, reindex_apply, submatrix_mul_equiv, reindex_apply]
  congr 1
  ext ((a | a) | a) ((b | b) | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.add_apply, add_assoc]

lemma eq_block3_of_blocks (M : B.Mat k (j + ρ)) :
    M = blk3 (bk M (q1 k ρ) (q1 k ρ)) (bk M (q1 k ρ) (q2 k j)) (bk M (q1 k ρ) (q3 k ρ))
      (bk M (q2 k j) (q1 k ρ)) (bk M (q2 k j) (q2 k j)) (bk M (q2 k j) (q3 k ρ))
      (bk M (q3 k ρ) (q1 k ρ)) (bk M (q3 k ρ) (q2 k j)) (bk M (q3 k ρ) (q3 k ρ)) := by
  ext x y
  obtain ⟨x', rfl⟩ := (eB k j ρ).surjective x
  obtain ⟨y', rfl⟩ := (eB k j ρ).surjective y
  rw [aux_statement_16]
  rcases x' with ((a | a) | a) <;> rcases y' with ((b | b) | b) <;> simp [bk, q1, q2, q3]

lemma entry_bound_block3 {c : ℝ} {A11 : Matrix (Fin j) (Fin j) ℂ} {A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : Matrix (Fin j) (Fin j) ℂ} {A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : B.Mat k ρ}
    {A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : Matrix (Fin j) (Fin j) ℂ}
    {A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : EB A11 c) (h12 : EB A12 c) (h13 : EB A13 c) (h21 : EB A21 c) (h22 : EB A22 c) (h23 : EB A23 c)
    (h31 : EB A31 c) (h32 : EB A32 c) (h33 : EB A33 c) : EB (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) c := by
  intro x y
  obtain ⟨x', rfl⟩ := (eB k j ρ).surjective x
  obtain ⟨y', rfl⟩ := (eB k j ρ).surjective y
  rw [aux_statement_16]
  rcases x' with ((a | a) | a) <;> rcases y' with ((b | b) | b) <;> simp only [fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, fromRows_apply_inl, fromRows_apply_inr,
    fromCols_apply_inl, fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

lemma det_Rn (x : RC k j ρ) : (Rn k j ρ x).det = 1 := by
  unfold Rn blk3
  rw [det_reindex_self, fromCols_zero, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp

end three

lemma entry_le_gN {k r : ℕ} (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by
  unfold B.gN
  rw [← Real.sqrt_sq (norm_nonneg (M i j))]
  apply Real.sqrt_le_sqrt
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (M i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

lemma gN_le_of_EB {k r : ℕ} (M : B.Mat k r) {c : ℝ} (h : EB M c) (hc : 0 ≤ c) :
    B.gN M ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c := by
  unfold B.gN
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (M i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), c ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * c) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

lemma EB_bk {k j ρ : ℕ} {ι κ : Type*} (M : B.Mat k (j + ρ)) (f : ι → Ix k j ρ) (f' : κ → Ix k j ρ) :
    EB (bk M f f') (B.gN M) :=
  fun a b => entry_le_gN M _ _

lemma wMat_mul_self (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, mul_apply, of_apply, one_apply]
  rw [Finset.sum_eq_single i.rev (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Fin.rev_rev]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

lemma wMat_ct (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext i j
  simp only [G.wMat, conjTranspose_apply, of_apply]
  by_cases h : j = i.rev
  · subst h
    simp [Fin.rev_rev]
  · have h' : ¬ i = j.rev := fun h'' => h (by rw [h'', Fin.rev_rev])
    simp [h, h']

lemma mul_w_w {j : ℕ} {ι : Type*} (M : Matrix (Fin j) ι ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, wMat_mul_self, Matrix.one_mul]

lemma skew_ct {j : ℕ} (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  unfold skewOf
  rw [conjTranspose_add, conjTranspose_sub, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have : (star fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) = -(fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) := by
    funext i
    simp [Complex.conj_ofReal]
  have hd : diagonal (-(fun i => Complex.I * ((q.2 i : ℝ) : ℂ))) =
      -diagonal (fun i => Complex.I * ((q.2 i : ℝ) : ℂ)) := by
    ext a b
    simp only [diagonal_apply, Matrix.neg_apply]
    split_ifs <;> simp
  rw [this, hd]
  abel

lemma beta_id {N j : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin N) (Fin j) ℂ)
    (S : Matrix (Fin j) (Fin j) ℂ) (hH : Hᴴ = H) (hS : Sᴴ = -S) :
    G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) =
      -(G.wMat j * (G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) - (-(G.wMat j * cᴴ * H)) * c)ᴴ *
        G.wMat j) := by
  set w := G.wMat j
  set X := cᴴ * H * c with hX
  have hXc : Xᴴ = X := by
    rw [hX, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  have h1 : (-(w * cᴴ * H)) * c = -(w * X) := by
    rw [hX, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : w * ((-(1 / 2 : ℂ)) • X + S) - -(w * X) = w * ((1 / 2 : ℂ) • X + S) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
    module
  rw [h1, h2, conjTranspose_mul, conjTranspose_add, conjTranspose_smul, hXc, hS, wMat_ct,
    Matrix.mul_assoc, Matrix.mul_assoc, wMat_mul_self, Matrix.mul_one]
  have h3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h3, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_neg]
  module

lemma EB_mulF {l n : Type*} {m : ℕ} {A : Matrix l (Fin m) ℂ} {B : Matrix (Fin m) n ℂ} {a b : ℝ}
    (hA : EB A a) (hB : EB B b) : EB (A * B) ((m : ℝ) * (a * b)) := by
  have := EB_mul hA hB
  rwa [Fintype.card_fin] at this

set_option maxHeartbeats 1000000 in
theorem _root_.Formalism.FourierDecayAlt.P.block3_apply_embedding : BigCellCoordinateSizes := by
  intro k j ρ hj
  have hj0 : j ≠ 0 := by omega
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = (j.factorial : ℝ) * (j : ℝ) ^ j := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = ((j - 1).factorial : ℝ) * (j : ℝ) ^ (j - 1) := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = (j : ℝ) ^ 2 * K0 := ⟨_, rfl⟩
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = ((2 * ρ + k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨nr, hnr⟩ : ∃ nr : ℝ, nr = ((2 * (j + ρ) + k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = Nr * (j : ℝ) + (j : ℝ) ^ 2 + 1 := ⟨_, rfl⟩
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  have hNr0 : 0 ≤ Nr := by rw [hNr]; positivity
  have hnr0 : 0 ≤ nr := by rw [hnr]; positivity
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hjr0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = nr * (A0 + K1 * K2) + (j : ℝ) + K0 + Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) :=
    ⟨_, rfl⟩
  have hCa : nr * (A0 + K1 * K2) ≤ C := by
    rw [hC]; have : 0 ≤ Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) := by positivity
    linarith
  have hCb : (j : ℝ) ≤ C := by
    rw [hC]; have : 0 ≤ Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) := by positivity
    have : 0 ≤ nr * (A0 + K1 * K2) := by positivity
    linarith
  have hCc : K0 ≤ C := by
    rw [hC]; have : 0 ≤ Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) := by positivity
    have : 0 ≤ nr * (A0 + K1 * K2) := by positivity
    linarith
  have hCd : Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) ≤ C := by
    rw [hC]; have : 0 ≤ nr * (A0 + K1 * K2) := by positivity
    linarith
  refine ⟨C, ?_⟩
  intro x x' Z γ hZ _hγ
  obtain ⟨hHct, hHH, -⟩ := hermitian_pos_facts_hold k ρ
  set w := G.wMat j with hw
  set H := Hpk k ρ with hH
  set c := Matrix.of x.1 with hc
  set S := skewOf x.2 with hS
  set α := -(w * cᴴ * H) with hα
  set β := w * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) with hβ
  set c' := Matrix.of x'.1 with hc'
  set α' := -(w * c'ᴴ * H) with hα'
  set β' := w * ((-(1 / 2 : ℂ)) • (c'ᴴ * H * c') + skewOf x'.2) with hβ'
  have hRn : Rn k j ρ x = blk3 1 α β 0 1 c 0 0 1 := rfl
  have hRn' : Rn k j ρ x' = blk3 1 α' β' 0 1 c' 0 0 1 := rfl
  have hmM : mMap k j ρ Z γ = blk3 0 0 (Zᴴ⁻¹ * w) 0 γ 0 (w * Z) 0 0 := rfl
  set g := (Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x' with hg
  set g' := B.gN g with hg'
  have hg'0 : 0 ≤ g' := Real.sqrt_nonneg _
  have key : Rn k j ρ x * g = mMap k j ρ Z γ * Rn k j ρ x' := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (by rw [det_Rn]; exact isUnit_one),
      Matrix.one_mul]
  set FourierUniquenessMirabolic := bk g (q1 k ρ) (q1 k ρ) with hG11
  set WeakApproximationGL := bk g (q1 k ρ) (q2 k j) with hG12
  set WhittakerVanishingImpliesZero := bk g (q1 k ρ) (q3 k ρ) with hG13
  set G21 := bk g (q2 k j) (q1 k ρ) with hG21
  set G22 := bk g (q2 k j) (q2 k j) with hG22
  set G23 := bk g (q2 k j) (q3 k ρ) with hG23
  set G31 := bk g (q3 k ρ) (q1 k ρ) with hG31
  set ContDiffOnLocalExtension := bk g (q3 k ρ) (q2 k j) with hG32
  set G33 := bk g (q3 k ρ) (q3 k ρ) with hG33
  have key2 := key
  rw [eq_block3_of_blocks g, hRn, hRn', hmM, block3_mul_blocks, block3_mul_blocks] at key2
  have ex : ∀ a b : Ix k j ρ, _ := fun a b => congrFun (congrFun key2 (eB k j ρ a)) (eB k j ρ b)
  have E31 : G31 = w * Z := by
    ext a b
    have := ex (q3 k ρ a) (q1 k ρ b)
    simpa [aux_statement_16, q1, q3] using this
  have E32 : ContDiffOnLocalExtension = w * Z * α' := by
    ext a b
    have := ex (q3 k ρ a) (q2 k j b)
    simpa [aux_statement_16, q2, q3] using this
  have E33 : G33 = w * Z * β' := by
    ext a b
    have := ex (q3 k ρ a) (q3 k ρ b)
    simpa [aux_statement_16, q3] using this
  have E21 : G21 + c * G31 = 0 := by
    ext a b
    have := ex (q2 k j a) (q1 k ρ b)
    simpa [aux_statement_16, q1, q2] using this
  have E22 : G22 + c * ContDiffOnLocalExtension = γ := by
    ext a b
    have := ex (q2 k j a) (q2 k j b)
    simpa [aux_statement_16, q2] using this
  have E11 : FourierUniquenessMirabolic + α * G21 + β * G31 = 0 := by
    ext a b
    have := ex (q1 k ρ a) (q1 k ρ b)
    simpa [aux_statement_16, q1] using this

  have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  set W := Z⁻¹ * w with hW
  have hνW : w * Z * W = 1 := by
    rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc Z, mul_nonsing_inv _ hZu, Matrix.one_mul, hw, wMat_mul_self]
  have hWν : W * (w * Z) = 1 := by
    rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc w, hw, wMat_mul_self, Matrix.one_mul, nonsing_inv_mul _ hZu]
  have hα'W : α' = W * ContDiffOnLocalExtension := by
    rw [E32, ← Matrix.mul_assoc, hWν, Matrix.one_mul]
  have hβ'W : β' = W * G33 := by
    rw [E33, ← Matrix.mul_assoc, hWν, Matrix.one_mul]
  have hG21' : G21 = -(c * (w * Z)) := by
    rw [← E31]
    exact eq_neg_of_add_eq_zero_left E21
  have hcW : c = -(G21 * W) := by
    rw [hG21', Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hνW, Matrix.mul_one]
  have hTW : β - α * c = -(FourierUniquenessMirabolic * W) := by
    have e1 : FourierUniquenessMirabolic = (α * c - β) * (w * Z) := by
      have e := E11
      rw [hG21', E31] at e
      calc FourierUniquenessMirabolic = (FourierUniquenessMirabolic + α * -(c * (w * Z)) + β * (w * Z)) + (α * (c * (w * Z)) - β * (w * Z)) := by
            rw [Matrix.mul_neg]; abel
        _ = (α * c - β) * (w * Z) := by rw [e, zero_add, Matrix.sub_mul, Matrix.mul_assoc α c]
    rw [e1, Matrix.mul_assoc, hνW, Matrix.mul_one, neg_sub]
  have hβT : β = -(w * (β - α * c)ᴴ * w) := beta_id H c S hHct (skew_ct x.2)
  have hc'α : c' = -(w * α' * H)ᴴ := by
    have e : w * α' * H = -c'ᴴ := by
      rw [hα', Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hHH,
        Matrix.mul_one, ← Matrix.mul_assoc w w, hw, wMat_mul_self, Matrix.one_mul]
    rw [e, conjTranspose_neg, conjTranspose_conjTranspose, neg_neg]
  have hγG : γ = G22 + c * ContDiffOnLocalExtension := E22.symm

  have hZw : Z = w * G31 := by rw [E31, hw, mul_w_w]
  have hZb : EB Z ((j : ℝ) * g') := by
    rw [hZw]
    exact (EB_mulF (EB_wMat j) (EB_bk g (q3 k ρ) (q1 k ρ))).mono (le_of_eq (by ring))
  set δ := ‖Z.det‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.mpr hZ
  have hδle : δ ≤ A0 * g' ^ j := by
    have := det_norm_le Z hZb
    rw [Fintype.card_fin, mul_pow] at this
    rw [hA0]
    linarith
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ0 : ℝ, ζ0 = ((j - 1).factorial : ℝ) * ((j : ℝ) * g') ^ (j - 1) / δ := ⟨_, rfl⟩
  have hζ00 : 0 ≤ ζ0 := by rw [hζ0]; positivity
  have hZib : EB Z⁻¹ ζ0 := by
    have := inv_entry_le Z hZb
    rwa [← hζ0] at this
  have hWb : EB W ((j : ℝ) * ζ0) := (EB_mulF hZib (EB_wMat j)).mono (le_of_eq (by ring))
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (j : ℝ) ^ 2 * ζ0 * g' := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hα'b : EB α' Y := by
    rw [hα'W]
    exact (EB_mulF hWb (EB_bk g (q3 k ρ) (q2 k j))).mono (le_of_eq (by rw [hY]; ring))
  have hβ'b : EB β' Y := by
    rw [hβ'W]
    exact (EB_mulF hWb (EB_bk g (q3 k ρ) (q3 k ρ))).mono (le_of_eq (by rw [hY]; ring))
  have hcb : EB c Y := by
    rw [hcW]
    exact (EB_neg (EB_mulF (EB_bk g (q2 k j) (q1 k ρ)) hWb)).mono (le_of_eq (by rw [hY]; ring))
  have hTb : EB (β - α * c) Y := by
    rw [hTW]
    exact (EB_neg (EB_mulF (EB_bk g (q1 k ρ) (q1 k ρ)) hWb)).mono (le_of_eq (by rw [hY]; ring))
  have hβb : EB β ((j : ℝ) ^ 2 * Y) := by
    rw [hβT]
    exact (EB_neg (EB_mulF (EB_mulF (EB_wMat j) (EB_conjTranspose hTb)) (EB_wMat j))).mono
      (le_of_eq (by ring))
  have hαb : EB α (Nr * (j : ℝ) * Y) := by
    rw [hα]
    exact (EB_neg (EB_mulF (EB_mulF (EB_wMat j) (EB_conjTranspose hcb)) (EB_Hpk k ρ))).mono
      (le_of_eq (by rw [hNr]; ring))
  have hc'b : EB c' (Nr * (j : ℝ) * Y) := by
    rw [hc'α]
    exact (EB_neg (EB_conjTranspose (EB_mulF (EB_mulF (EB_wMat j) hα'b) (EB_Hpk k ρ)))).mono
      (le_of_eq (by rw [hNr]; ring))
  have hγb : EB γ (g' + (j : ℝ) * (Y * g')) := by
    rw [hγG]
    exact EB_add (EB_bk g (q2 k j) (q2 k j)) (EB_mulF hcb (EB_bk g (q3 k ρ) (q2 k j)))

  have hB1 : (1 : ℝ) ≤ 1 + K1 * Y := le_add_of_nonneg_right (mul_nonneg hK10 hY0)
  have hK1Y : K1 * Y = Nr * (j : ℝ) * Y + (j : ℝ) ^ 2 * Y + Y := by rw [hK1]; ring
  have hp1 : 0 ≤ Nr * (j : ℝ) * Y := by positivity
  have hp2 : 0 ≤ (j : ℝ) ^ 2 * Y := by positivity
  have hnb : EB (Rn k j ρ x) (1 + K1 * Y) := by
    rw [hRn]
    refine entry_bound_block3 (EB_one.mono hB1) (hαb.mono ?_) (hβb.mono ?_) (EB_zero.mono (by linarith))
      (EB_one.mono hB1) (hcb.mono ?_) (EB_zero.mono (by linarith)) (EB_zero.mono (by linarith)) (EB_one.mono hB1)
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith
  have hn'b : EB (Rn k j ρ x') (1 + K1 * Y) := by
    rw [hRn']
    refine entry_bound_block3 (EB_one.mono hB1) (hα'b.mono ?_) (hβ'b.mono ?_) (EB_zero.mono (by linarith))
      (EB_one.mono hB1) (hc'b.mono ?_) (EB_zero.mono (by linarith)) (EB_zero.mono (by linarith)) (EB_one.mono hB1)
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith
    · rw [hK1Y]; linarith

  have hYg : Y = K2 * (g' ^ j / δ) := by
    rw [hY, hζ0, hK2, hK0, mul_pow, ← pow_sub_one_mul hj0 g']
    field_simp
  set μ := min 1 δ with hμ
  have hμ0 : 0 < μ := lt_min one_pos hδ0
  have hμδ : μ ≤ δ := min_le_right _ _
  have hgj0 : 0 ≤ g' ^ j := pow_nonneg hg'0 j
  set R := g' ^ j / μ with hR
  have hR0 : 0 ≤ R := by positivity
  have hQR : g' ^ j / δ ≤ R := div_le_div_of_nonneg_left hgj0 hμ0 hμδ
  have hA0R : 1 ≤ A0 * R := by
    rw [hR, mul_div_assoc', le_div_iff₀ hμ0]
    linarith
  have hYR : Y ≤ K2 * R := by rw [hYg]; exact mul_le_mul_of_nonneg_left hQR hK20
  have hRn_le : ∀ M : B.Mat k (j + ρ), EB M (1 + K1 * Y) → B.gN M ≤ C * g' ^ j / μ := by
    intro M hM
    have h1 := gN_le_of_EB M hM (by linarith)
    rw [← hnr] at h1
    calc B.gN M ≤ nr * (1 + K1 * Y) := h1
      _ ≤ nr * (A0 * R + K1 * (K2 * R)) := by
          apply mul_le_mul_of_nonneg_left _ hnr0
          have := mul_le_mul_of_nonneg_left hYR hK10
          linarith
      _ = nr * (A0 + K1 * K2) * R := by ring
      _ ≤ C * R := mul_le_mul_of_nonneg_right hCa hR0
      _ = C * g' ^ j / μ := by rw [hR, mul_div_assoc]
  refine ⟨hRn_le _ hnb, hRn_le _ hn'b, ?_, ?_, ?_⟩
  ·
    exact (mx_le hZb (by positivity)).trans (mul_le_mul_of_nonneg_right hCb hg'0)
  ·
    refine (mx_le hZib hζ00).trans ?_
    rw [hζ0, mul_pow]
    have : ((j - 1).factorial : ℝ) * ((j : ℝ) ^ (j - 1) * g' ^ (j - 1)) = K0 * g' ^ (j - 1) := by
      rw [hK0]; ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) hδ0.le
  ·
    have h1 := gN_le_of_EB γ hγb (by positivity)
    rw [← hNr] at h1
    have hsq : 1 ≤ (A0 * R) ^ 2 := one_le_pow₀ hA0R
    have e1 : g' ≤ A0 ^ 2 * (g' * R ^ 2) := by
      have := mul_le_mul_of_nonneg_left hsq hg'0
      nlinarith
    have e2 : (j : ℝ) * (Y * g') ≤ (j : ℝ) * K2 * A0 * (g' * R ^ 2) := by
      have h3 : Y * g' ≤ K2 * R * g' := mul_le_mul_of_nonneg_right hYR hg'0
      have h4 : K2 * R * g' ≤ K2 * R * g' * (A0 * R) := le_mul_of_one_le_right (by positivity) hA0R
      have h5 : (j : ℝ) * (Y * g') ≤ (j : ℝ) * (K2 * R * g' * (A0 * R)) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) hjr0
      calc (j : ℝ) * (Y * g') ≤ (j : ℝ) * (K2 * R * g' * (A0 * R)) := h5
        _ = (j : ℝ) * K2 * A0 * (g' * R ^ 2) := by ring
    have e3 : g' * R ^ 2 = g' ^ (2 * j + 1) / μ ^ 2 := by
      rw [hR, div_pow, ← pow_mul, pow_succ]
      ring
    calc B.gN γ ≤ Nr * (g' + (j : ℝ) * (Y * g')) := h1
      _ ≤ Nr * (A0 ^ 2 * (g' * R ^ 2) + (j : ℝ) * K2 * A0 * (g' * R ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hNr0
          linarith
      _ = Nr * (A0 ^ 2 + (j : ℝ) * K2 * A0) * (g' * R ^ 2) := by ring
      _ ≤ C * (g' * R ^ 2) := mul_le_mul_of_nonneg_right hCd (by positivity)
      _ = C * g' ^ (2 * j + 1) / μ ^ 2 := by rw [e3, mul_div_assoc]

end Formalism.FourierDecayAlt.P.Ux5
