import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLeastSquaresBoundStatement

open scoped ComplexOrder Matrix

namespace GlobalTheory

namespace WeightedInverseBound

theorem wls_fintype {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (L : Matrix ι (Fin g) ℝ)
    (hL : L.rank = g) : ∃ K : ℝ, ∀ (D : ι → ℝ) (b : ι → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖
        ≤ K * ‖b‖ := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hr : (L.submatrix e (Equiv.refl (Fin g))).rank = g := by
    rw [Matrix.rank_submatrix]; exact hL
  obtain ⟨K, hK⟩ := GlobalTheory.T.exists_norm_weighted_least_squares_le _ g _ hr
  refine ⟨K, fun D b hD => ?_⟩
  have h := hK (D ∘ e) (b ∘ e) (fun k => hD _)
  have h1 : (L.submatrix e (Equiv.refl (Fin g))).transpose * Matrix.diagonal (D ∘ e) *
      (L.submatrix e (Equiv.refl (Fin g))) = L.transpose * Matrix.diagonal D * L := by
    ext i j
    simp only [Matrix.mul_apply (M := _ * Matrix.diagonal _), Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.refl_apply, Function.comp]
    exact e.sum_comp (fun k => L k i * D k * L k j)
  have h2 : ((L.submatrix e (Equiv.refl (Fin g))).transpose * Matrix.diagonal (D ∘ e)).mulVec
      (b ∘ e) = (L.transpose * Matrix.diagonal D).mulVec b := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.refl_apply, Function.comp]
    exact e.sum_comp (fun k => L k i * D k * b k)
  have h3 : ‖b ∘ e‖ = ‖b‖ := e.surjective.pi_norm_comp b
  rw [h1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h2, h3] at h
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  exact h

theorem dot_le_card_mul_norm_mul_norm {g : ℕ} (x y : Fin g → ℝ) : x ⬝ᵥ y ≤ g * (‖x‖ * ‖y‖) := by
  calc x ⬝ᵥ y = ∑ k, x k * y k := rfl
    _ ≤ ∑ _k : Fin g, ‖x‖ * ‖y‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm x k) (norm_le_pi_norm y k) (abs_nonneg _)
          (norm_nonneg _)
    _ = g * (‖x‖ * ‖y‖) := by simp

theorem norm_sq_le_dot {g : ℕ} (x : Fin g → ℝ) : ‖x‖ * ‖x‖ ≤ x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have : ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    rw [sq]
    exact Finset.single_le_sum (f := fun k => x k * x k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ k)
  calc ‖x‖ * ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (x ⬝ᵥ x) :=
        mul_le_mul this this (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = x ⬝ᵥ x := Real.mul_self_sqrt h0

theorem norm_le_of_coercive {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) (z : Fin g → ℝ) :
    ‖z‖ ≤ g / c * ‖Y.mulVec z‖ := by
  rcases (norm_nonneg z).eq_or_lt with h | h
  · rw [← h]; positivity
  have h1 := hY z
  have h2 := dot_le_card_mul_norm_mul_norm z (Y.mulVec z)
  have h3 := norm_sq_le_dot z
  have h4 : ‖z‖ * (c * ‖z‖) ≤ ‖z‖ * (g * ‖Y.mulVec z‖) := by nlinarith
  have h5 := le_of_mul_le_mul_left h4 h
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

theorem isUnit_det_of_coercive {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) : IsUnit Y.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h := norm_le_of_coercive hc hY (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

theorem norm_mulVec_le {m : Type} [Fintype m] {g : ℕ} {Y : Matrix m (Fin g) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ j k, |Y j k| ≤ C) (z : Fin g → ℝ) :
    ‖Y.mulVec z‖ ≤ g * C * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  calc ‖Y.mulVec z j‖ = |∑ k, Y j k * z k| := rfl
    _ ≤ ∑ k, |Y j k * z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin g, C * ‖z‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (h j k) (norm_le_pi_norm z k) (abs_nonneg _) hC
    _ = g * C * ‖z‖ := by simp [mul_assoc]

theorem abs_entry_le {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {C : ℝ} (hs : Y.IsSymm)
    (h0 : ∀ x, 0 ≤ x ⬝ᵥ Y.mulVec x) (h1 : ∀ x, x ⬝ᵥ Y.mulVec x ≤ C * (x ⬝ᵥ x)) (j k : Fin g) :
    |Y j k| ≤ |C| := by
  have a := h1 (Pi.single j 1)
  have b := h1 (Pi.single k 1)
  have p := h0 (Pi.single j 1 + Pi.single k 1)
  have q := h0 (Pi.single j 1 - Pi.single k 1)
  have s : Y k j = Y j k := hs.apply j k
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, single_dotProduct, Matrix.mulVec_single_one, one_mul,
    Matrix.col_apply, Pi.single_eq_same, mul_one] at a b p q
  have := le_abs_self C
  rw [abs_le]
  constructor <;> linarith

theorem bound_one_add {g a : ℕ} (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (hB : ∀ i, (B i).PosSemidef) : ∃ K : ℝ, ∀ t : Fin a → ℝ, (∀ i, 0 < t i) → ∀ i x,
      ‖(1 + ∑ l, t l • B l)⁻¹.mulVec ((t i • B i).mulVec x)‖ ≤ K * ‖x‖ := by
  classical
  have hR : ∀ i, ∃ R : Matrix (Fin g) (Fin g) ℝ, B i = R.transpose * R := by
    intro i
    open scoped MatrixOrder in
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (hB i).nonneg
    exact ⟨R, by rw [hR]; rfl⟩
  choose R hR using hR
  let L : Matrix (Fin g ⊕ (Fin a × Fin g)) (Fin g) ℝ :=
    Matrix.fromRows 1 (Matrix.of fun p j => R p.1 p.2 j)
  have hL : L.rank = g := by
    refine le_antisymm (by simpa using L.rank_le_card_width) ?_
    have h1 : (Matrix.fromCols (1 : Matrix (Fin g) (Fin g) ℝ)
        (0 : Matrix (Fin g) (Fin a × Fin g) ℝ)) * L = 1 := by
      simp [L, Matrix.fromCols_mul_fromRows]
    have h2 := Matrix.rank_mul_le_right (Matrix.fromCols (1 : Matrix (Fin g) (Fin g) ℝ)
        (0 : Matrix (Fin g) (Fin a × Fin g) ℝ)) L
    rw [h1, Matrix.rank_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨K, hK⟩ := wls_fintype L hL
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ i j k, |R i j k| ≤ A :=
    ⟨‖fun i j k => R i j k‖, norm_nonneg _, fun i j k =>
      ((norm_le_pi_norm _ k).trans (norm_le_pi_norm (fun j k => R i j k) j)).trans
        (norm_le_pi_norm (fun i j k => R i j k) i)⟩
  refine ⟨|K| * (g * A), fun t ht i x => ?_⟩
  let D : Fin g ⊕ (Fin a × Fin g) → ℝ := Sum.elim (fun _ => 1) (fun p => t p.1)
  let b : Fin g ⊕ (Fin a × Fin g) → ℝ :=
    Sum.elim (fun _ => 0) (fun p => if p.1 = i then (R i).mulVec x p.2 else 0)
  have hD : ∀ k, 0 < D k := by
    rintro (k | p)
    · exact one_pos
    · exact ht _
  have h := hK D b hD
  have h1 : L.transpose * Matrix.diagonal D * L = 1 + ∑ l, t l • B l := by
    ext j k
    simp only [Matrix.mul_apply (M := _ * Matrix.diagonal _), Matrix.mul_diagonal,
      Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, L, D,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hR,
      Matrix.mul_apply (N := R _), smul_eq_mul, Finset.mul_sum]
    congr 1
    · simp [Matrix.one_apply, eq_comm]
    · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  have h2 : (L.transpose * Matrix.diagonal D).mulVec b = (t i • B i).mulVec x := by
    rw [hR i, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, L, D, b,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      rw [Finset.mul_sum Finset.univ _ (t i)]
      exact Finset.sum_congr rfl fun m _ => by ring
    · intro l _ hl
      simp [hl]
    · simp
  have h3 : ‖b‖ ≤ g * A * ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
    rintro (k | p)
    · simp only [b, Sum.elim_inl, norm_zero]; positivity
    · simp only [b, Sum.elim_inr]
      split_ifs
      · exact (norm_le_pi_norm _ _).trans (norm_mulVec_le hA0 (hA i) x)
      · simp only [norm_zero]; positivity
  rw [h1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h2] at h
  calc _ ≤ K * ‖b‖ := h
    _ ≤ |K| * ‖b‖ := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
    _ ≤ |K| * (g * A * ‖x‖) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = _ := by ring

end WeightedInverseBound

open WeightedInverseBound in

theorem smul_inv_mul_posSemidef_uniform_bound : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by
  intro g a B c C hc hB
  obtain ⟨K, hK⟩ := bound_one_add B hB
  refine ⟨(1 + g / c * (1 + g * |C|)) * K, fun Y' t hs hlo hhi ht i x => ?_⟩
  have hw := hK t ht i x
  set P := ∑ l, t l • B l with hP
  have hP0 : ∀ z, 0 ≤ z ⬝ᵥ P.mulVec z := by
    intro z
    have : P.PosSemidef := Matrix.posSemidef_sum _ fun l _ => (hB l).smul (ht l).le
    simpa using this.dotProduct_mulVec_nonneg z
  have hY : ∀ z, c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Y' + P).mulVec z := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add]
    linarith [hlo z, hP0 z]
  have hZ : ∀ z, 1 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (1 + P).mulVec z := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
    linarith [hP0 z]
  have hYu := isUnit_det_of_coercive hc hY
  have hZu := isUnit_det_of_coercive one_pos hZ
  set v := (t i • B i).mulVec x with hv
  set w := (1 + P)⁻¹.mulVec v with hwdef
  have hu : (t i • ((Y' + P)⁻¹ * B i)).mulVec x = (Y' + P)⁻¹.mulVec v := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_smul]
  rw [hu]
  set u := (Y' + P)⁻¹.mulVec v with hudef
  have e1 : (Y' + P).mulVec u = v := by
    rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hYu, Matrix.one_mulVec]
  have e2 : (1 + P).mulVec w = v := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mulVec]
  have e3 : (Y' + P).mulVec (u - w) = w - Y'.mulVec w := by
    rw [Matrix.mulVec_sub, e1, ← e2, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    abel
  have h0 : ∀ z, 0 ≤ z ⬝ᵥ Y'.mulVec z := fun z =>
    le_trans (mul_nonneg hc.le (le_trans (mul_self_nonneg _) (norm_sq_le_dot z))) (hlo z)
  have b1 := norm_mulVec_le (abs_nonneg C) (abs_entry_le hs h0 hhi) w
  have b2 := norm_le_of_coercive hc hY (u - w)
  rw [e3] at b2
  have b3 : ‖w - Y'.mulVec w‖ ≤ (1 + g * |C|) * ‖w‖ := by
    have := norm_sub_le w (Y'.mulVec w)
    linarith
  have b4 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
    have := norm_add_le w (u - w)
    rwa [add_sub_cancel] at this
  have hgc : (0 : ℝ) ≤ g / c := by positivity
  have b5 := mul_le_mul_of_nonneg_left b3 hgc
  calc ‖u‖ ≤ (1 + g / c * (1 + g * |C|)) * ‖w‖ := by linarith
    _ ≤ (1 + g / c * (1 + g * |C|)) * (K * ‖x‖) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

end GlobalTheory
