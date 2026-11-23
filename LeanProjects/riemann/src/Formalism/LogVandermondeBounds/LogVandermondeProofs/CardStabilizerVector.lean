import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

lemma half_add_half (n : ℕ) : n * (n - 1) / 2 + n * (n + 1) / 2 = n * n := by
  rcases n with _ | k
  · simp
  · obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    have h1 : (k + 1) * k = m + m := by rw [mul_comm]; exact hm
    have h2 : (k + 1) * (k + 1 + 1) = m + m + 2 * (k + 1) := by rw [← h1]; ring
    have h3 : (k + 1) * (k + 1) = m + m + (k + 1) := by rw [← h1]; ring
    rw [Nat.add_sub_cancel, h1, h2, h3]
    omega

lemma factor_eq (q : ℝ) (hq : q ≠ 0) (n i : ℕ) (hi : i ≤ n) :
    q ^ n - q ^ i = q ^ n * (1 - q⁻¹ ^ (n - i)) := by
  have h : q ^ n * q⁻¹ ^ (n - i) = q ^ i := by
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hq), ← pow_add, Nat.add_sub_of_le hi]
  rw [mul_sub, mul_one, h]

theorem cardGeneralLinear : CardGeneralLinear := by
  intro F _ _ _ n
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnat : Fintype.card (GL (Fin n) F) =
      ∏ i ∈ range n, (Fintype.card F ^ n - Fintype.card F ^ i) := by
    rw [Finset.prod_range, Fintype.card_eq_nat_card (α := GL (Fin n) F)]
    exact Matrix.card_GL_field n
  have hreal : (Fintype.card (GL (Fin n) F) : ℝ) =
      ∏ i ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i) := by
    rw [hnat, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Nat.cast_sub (Nat.pow_le_pow_right hpos (mem_range.mp hi).le), Nat.cast_pow, Nat.cast_pow]
  rw [hreal, ← pow_add, half_add_half]
  have hpow : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i ∈ range n, (Fintype.card F : ℝ) ^ n := by
    rw [prod_const, card_range, ← pow_mul]
  have hrefl : ∏ j ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ (n - 1 - j)) =
      ∏ j ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ j) :=
    prod_range_reflect (fun i => (Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i) n
  rw [hpow, ← prod_mul_distrib, ← hrefl]
  refine prod_congr rfl (fun i hi => ?_)
  have hi' := mem_range.mp hi
  rw [factor_eq _ hq0 n (n - 1 - i) (by omega), show n - (n - 1 - i) = i + 1 by omega]

def upperEquiv (F : Type) [Field F] (n : ℕ) :
    {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} ≃
      ({p : Fin n × Fin n // p.1 < p.2} → F) where
  toFun A p := A.1 p.1.1 p.1.2
  invFun f := ⟨fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · simp [not_lt.mpr hji.le, hji.ne']
    · simp⟩
  left_inv A := by
    apply Subtype.ext
    funext i j
    simp only
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (A.2.2 i).symm
    · exact (A.2.1 i j (lt_of_le_of_ne (not_lt.mp h1) (fun h => h2 h.symm))).symm
  right_inv f := by
    funext p
    simp [p.2]

lemma card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have hs : (univ.filter (fun i : Fin n => i < j)) = Finset.Iio j := by ext i; simp
    rw [hs, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

theorem cardUnitriangular : CardUnitriangular := by
  intro F _ _ _ n
  rw [Nat.card_congr (upperEquiv F n)]
  rw [Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

def RowVec (F : Type) (n : ℕ) : Type := Fin n → F

instance rowVecFinite (F : Type) [Finite F] (n : ℕ) : Finite (RowVec F n) :=
  inferInstanceAs (Finite (Fin n → F))

instance rowAction (F : Type) [Field F] (n : ℕ) : MulAction (GL (Fin n) F) (RowVec F n) where
  smul g v := Matrix.vecMul (v : Fin n → F) ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  one_smul v := by
    show Matrix.vecMul (v : Fin n → F)
      (((1 : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v
    rw [inv_one, Units.val_one]
    exact Matrix.vecMul_one _
  mul_smul g h v := by
    show Matrix.vecMul (v : Fin n → F) (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.vecMul (Matrix.vecMul (v : Fin n → F) ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [mul_inv_rev, Units.val_mul]
    exact (Matrix.vecMul_vecMul (v : Fin n → F) _ _).symm

lemma vecMul_inv_eq_iff {F : Type} [Field F] {n : ℕ} (v : Fin n → F) (A : GL (Fin n) F) :
    Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v ↔
      Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v := by
  constructor
  · intro h
    calc Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F)
        = Matrix.vecMul (Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
            (A : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  · intro h
    calc Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = Matrix.vecMul (Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F))
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

private theorem vecMul_one_add_vecMulVec_single {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (c z : Fin n → F) :
    Matrix.vecMul z (1 + Matrix.vecMulVec (Pi.single k 1) c) = z + z k • c := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  congr 1
  funext j
  simp [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply]

private theorem single_one_vecMul_apply {F : Type} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Matrix.vecMul (Pi.single i 1) M j = M i j := by
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

private theorem one_add_vecMulVec_single_mul_inverse_eq_one {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (x y : Fin n → F) (hx : x k ≠ 0) (hy : y k ≠ 0) :
    (1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) *
      (1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y))) = 1 := by
  have key : ∀ z : Fin n → F, Matrix.vecMul z
      ((1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) *
        (1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y)))) = z := by
    intro z
    rw [← Matrix.vecMul_vecMul, vecMul_one_add_vecMulVec_single,
      vecMul_one_add_vecMulVec_single]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  ext i j
  have h1 := congrFun (key (Pi.single i 1)) j
  rw [single_one_vecMul_apply] at h1
  rw [h1]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem exists_GL_vecMul_eq_of_ne_zero_at {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (x y : Fin n → F) (hx : x k ≠ 0) (hy : y k ≠ 0) :
    ∃ A : GL (Fin n) F, Matrix.vecMul x (A : Matrix (Fin n) (Fin n) F) = y := by
  refine ⟨(⟨1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x)),
    1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y)),
    one_add_vecMulVec_single_mul_inverse_eq_one k x y hx hy,
    one_add_vecMulVec_single_mul_inverse_eq_one k y x hy hx⟩ : (Matrix (Fin n) (Fin n) F)ˣ), ?_⟩
  show Matrix.vecMul x (1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) = y
  rw [vecMul_one_add_vecMulVec_single]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [mul_inv_cancel_left₀ hx]
  ring

lemma exists_row {F : Type} [Field F] [Fintype F] {n : ℕ} (v w : Fin n → F) (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ A : GL (Fin n) F, Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = w := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨l, hl⟩ : ∃ l, w l ≠ 0 := by
    by_contra h
    exact hw (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨A, hA⟩ := exists_GL_vecMul_eq_of_ne_zero_at k v (fun _ : Fin n => (1 : F)) hk one_ne_zero
  obtain ⟨B, hB⟩ := exists_GL_vecMul_eq_of_ne_zero_at l (fun _ : Fin n => (1 : F)) w one_ne_zero hl
  refine ⟨A * B, ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, hA, hB]

theorem cardStabilizerVector : CardStabilizerVector := by
  intro F _ _ _ n v hv
  have hcardne : Fintype.card {w : Fin n → F // w ≠ 0} = Fintype.card F ^ n - 1 := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : Fin n → F))
    rw [Fintype.card_option, Fintype.card_fun, Fintype.card_fin] at h
    omega
  have horbit : Nat.card (@MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v) =
      Fintype.card F ^ n - 1 := by
    have e : @MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v ≃ {w : Fin n → F // w ≠ 0} :=
      Equiv.subtypeEquivRight (fun w => by
        refine MulAction.mem_orbit_iff.trans ?_
        constructor
        · rintro ⟨g, rfl⟩ h0
          apply hv
          have h1 : Matrix.vecMul (Matrix.vecMul v ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
              (g : Matrix (Fin n) (Fin n) F) = v := by
            rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
          have h0' : Matrix.vecMul v ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0 := h0
          rw [← h1, h0', Matrix.zero_vecMul]
        · intro hw0
          obtain ⟨A, hA⟩ := exists_row v w hv hw0
          refine ⟨A⁻¹, ?_⟩
          show Matrix.vecMul v (((A⁻¹)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = w
          rw [inv_inv, hA])
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, hcardne]
  have hstab : Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} =
      Nat.card (@MulAction.stabilizer (GL (Fin n) F) (RowVec F n) _ _ v) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun A => by
      exact (vecMul_inv_eq_iff v A).symm))
  have hos : Nat.card (@MulAction.stabilizer (GL (Fin n) F) (RowVec F n) _ _ v) *
      Nat.card (@MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v) = Nat.card (GL (Fin n) F) := by
    first
    | (rw [← MulAction.index_stabilizer]; exact Subgroup.card_mul_index _)
    | (rw [mul_comm]; exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ _)
    | (rw [mul_comm, ← Nat.card_prod]; exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ _))
  rw [hstab, ← horbit, hos, Nat.card_eq_fintype_card]

end Formalism.LogVandermondeBounds.StandardLattice
