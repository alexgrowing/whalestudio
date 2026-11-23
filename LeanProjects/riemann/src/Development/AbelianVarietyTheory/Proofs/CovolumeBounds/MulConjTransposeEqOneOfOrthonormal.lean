import Mathlib

open Matrix

namespace GlobalTheory

section Ring

variable {R : Type*} [CommRing R]

abbrev subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) : Fin i → n :=
  S.1.orderEmbOfFin S.2

theorem range_subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) :=
  Finset.range_orderEmbOfFin _ _

theorem subsetEnum_injective {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Function.Injective (subsetEnum S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem alternatingMap_apply_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (f : (n → R) [⋀^Fin i]→ₗ[R] M)
    (A : Fin i → n → R) :
    f A = ∑ S : Set.powersetCard n i,
      ((Matrix.of A).submatrix id (subsetEnum S)).det • f (fun a => Pi.single (subsetEnum S a) 1) := by
  classical
  let b := Pi.basisFun R n
  have h := (b.exteriorPower i).sum_repr (exteriorPower.ιMulti R i A)
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f A, ← h, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_smul, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  congr 2
  funext a
  simp only [b, Function.comp_apply, Pi.basisFun_apply]
  rfl

theorem det_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by
  classical
  have h := alternatingMap_apply_eq_sum_minors
    ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A
  have h0 : (A * B).det =
      ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A := rfl
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [AlternatingMap.compLinearMap_apply]
  change Matrix.det _ = _
  congr 1
  ext a c
  simp [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]

theorem det_mul_det_eq_of_range_eq {m k n : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix m n R) (B : Matrix n m R) (φ : k ≃ m) (e : m → n) (g : k → n)
    (hg : Function.Injective g) (h : Set.range e = Set.range g) :
    (A.submatrix id e).det * (B.submatrix e id).det =
      (A.submatrix φ g).det * (B.submatrix g φ).det := by
  have h1 : ∀ a : k, ∃ c : m, e c = g a := fun a => by
    have : g a ∈ Set.range e := h ▸ Set.mem_range_self a
    exact this
  choose s hs using h1
  have hinj : Function.Injective (φ.symm ∘ s) := by
    intro a a' haa
    have : s a = s a' := φ.symm.injective haa
    exact hg (by rw [← hs a, ← hs a', this])
  let σ : Equiv.Perm k := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ a, e (φ (σ a)) = g a := fun a => by simp [σ, hs]
  have hA : A.submatrix φ g = ((A.submatrix id e).submatrix φ φ).submatrix id σ := by
    ext a c; simp [hσ]
  have hB : B.submatrix g φ = ((B.submatrix e id).submatrix φ φ).submatrix σ id := by
    ext a c; simp [hσ]
  rw [hA, hB, det_permute, det_permute', det_submatrix_equiv_self, det_submatrix_equiv_self]
  have : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  linear_combination (-(A.submatrix id e).det * (B.submatrix e id).det) * this

theorem det_mul_eq_sum_minors_of_enum {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (e : Set.powersetCard n (Fintype.card m) → m → n)
    (he : ∀ S, Set.range (e S) = (S.1 : Set n)) (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ S : Set.powersetCard n (Fintype.card m),
      (A.submatrix id (e S)).det * (B.submatrix (e S) id).det := by
  classical
  letI : LinearOrder n := linearOrderOfSTO WellOrderingRel
  let φ : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  rw [← det_submatrix_equiv_self φ (A * B), submatrix_mul A B φ id φ Function.bijective_id,
    det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [det_mul_det_eq_of_range_eq A B φ (e S) (subsetEnum S) (subsetEnum_injective S)
    ((he S).trans (range_subsetEnum S).symm)]
  rfl

theorem det_submatrix_mul_eq_sum_minors {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [submatrix_mul A B r id c Function.bijective_id, det_mul_eq_sum_minors]
  rfl

theorem det_mul_diagonal_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (d : n → R) (B : Matrix n (Fin i) R) :
    (A * diagonal d * B).det = ∑ S : Set.powersetCard n i,
      (∏ s ∈ S.1, d s) *
        ((A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det) := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (A * diagonal d).submatrix id (subsetEnum S) =
      A.submatrix id (subsetEnum S) * diagonal (d ∘ subsetEnum S) := by
    ext a c; simp
  have h2 : ∏ a, d (subsetEnum S a) = ∏ s ∈ S.1, d s := by
    refine Finset.prod_bij (fun a _ => subsetEnum S a) (fun a _ => Finset.orderEmbOfFin_mem _ _ _)
      (fun a _ b _ h => subsetEnum_injective S h) (fun s hs => ?_) (fun _ _ => rfl)
    have : s ∈ Set.range (subsetEnum S) := by rw [range_subsetEnum]; exact hs
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_univ _, ha⟩
  rw [h1, det_mul, det_diagonal, ← h2]
  simp only [Function.comp_apply]
  ring

end Ring

section Normed

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}

theorem det_mul_conjTranspose_eq_sum_norm_sq (A : Matrix (Fin i) n 𝕜) :
    (A * Aᴴ).det =
      ((∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_minors]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]

theorem sum_norm_sq_minors_eq_one (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq A
  rw [hA, det_one] at h
  exact_mod_cast h.symm

theorem two_rpow_neg_half_le_choose_rpow {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < N.choose i := by exact_mod_cast Nat.choose_pos hi
  have hle : (N.choose i : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.choose_le_two_pow N i).trans (Nat.pow_le_pow_right two_pos hr)
  calc (2 : ℝ) ^ (-(r : ℝ) / 2) = ((2 : ℝ) ^ (r : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)

theorem exists_choose_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by
  have h := sum_norm_sq_minors_eq_one A hA
  have hne : (Finset.univ : Finset (Set.powersetCard n i)).Nonempty := by
    rcases (Finset.univ : Finset (Set.powersetCard n i)).eq_empty_or_nonempty with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hi : i ≤ Fintype.card n := by
    obtain ⟨S, -⟩ := hne
    exact S.2 ▸ Finset.card_le_univ S.1
  have hcard : Fintype.card (Set.powersetCard n i) = (Fintype.card n).choose i := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hpos : (0 : ℝ) < (Fintype.card n).choose i := by exact_mod_cast Nat.choose_pos hi
  refine ⟨hi, ?_⟩
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (((Fintype.card n).choose i : ℝ))⁻¹)
    (g := fun S => ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2) (by
      rw [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])
  refine ⟨S, (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_⟩
  refine le_of_eq_of_le ?_ hS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
  norm_num

theorem exists_two_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by
  obtain ⟨hi, S, hS⟩ := exists_choose_rpow_le_norm_minor A hA
  exact ⟨S, (two_rpow_neg_half_le_choose_rpow hi hr).trans hS⟩

end Normed

end GlobalTheory
