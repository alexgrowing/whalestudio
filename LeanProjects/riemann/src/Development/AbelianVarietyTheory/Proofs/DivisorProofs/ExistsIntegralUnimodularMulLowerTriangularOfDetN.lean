import Mathlib
open Matrix

namespace GlobalTheory
namespace IwasawaLowerTri

variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F]

lemma permMatrix_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix V).map (algebraMap V F) = σ.permMatrix F := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma permMatrix_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (σ.permMatrix F * A) i j = A (σ i) j := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]

lemma isUnit_det_permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsUnit (σ.permMatrix V).det := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma exists_max_val {n : ℕ} (c : Fin (n+1) → F) :
    ∃ i0, ∀ i, ValuationRing.valuation V F (c i) ≤ ValuationRing.valuation V F (c i0) := by
  obtain ⟨i0, -, h⟩ := Finset.exists_max_image Finset.univ (fun i => ValuationRing.valuation V F (c i)) Finset.univ_nonempty
  exact ⟨i0, fun i => h i (Finset.mem_univ _)⟩

lemma integral_of_val_le (x y : F) (hy : y ≠ 0)
    (h : ValuationRing.valuation V F x ≤ ValuationRing.valuation V F y) :
    ∃ q : V, algebraMap V F q = x / y := by
  rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_div]
  have : ValuationRing.valuation V F y ≠ 0 := by simpa using hy
  exact (div_le_one₀ (zero_lt_iff.mpr this)).mpr h

lemma clear_last_column {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F) :
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) V, IsUnit P.det ∧
      ∀ i : Fin n, (P.map (algebraMap V F) * A) i.castSucc (Fin.last n) = 0 := by
  by_cases hz : ∀ i, A i (Fin.last n) = 0
  · refine ⟨1, by simp, fun i => ?_⟩
    simp [hz]
  push_neg at hz
  obtain ⟨i1, hi1⟩ := hz
  obtain ⟨i0, hmax⟩ := exists_max_val V F (fun i => A i (Fin.last n))
  have h0 : A i0 (Fin.last n) ≠ 0 := by
    intro h
    have := hmax i1
    simp only [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi1 this
  have hq : ∀ i, ∃ q : V, algebraMap V F q = A i (Fin.last n) / A i0 (Fin.last n) :=
    fun i => integral_of_val_le V F _ _ h0 (hmax i)
  choose q hq using hq
  set σ : Equiv.Perm (Fin (n+1)) := Equiv.swap i0 (Fin.last n) with hσ
  let E : Matrix (Fin (n+1)) (Fin (n+1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = Fin.last n then -q (σ i) else 0
  refine ⟨E * σ.permMatrix V, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ (isUnit_det_permMatrix V σ)
    rw [Matrix.det_of_upperTriangular]
    · simp [E]
    · intro a b hab
      have hne : a ≠ b := ne_of_gt hab
      have hb : b ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hab (Fin.le_last a))
      simp [E, hne, hb]
  · rw [Matrix.map_mul, Matrix.mul_assoc, permMatrix_map, Matrix.mul_apply,
      Fintype.sum_eq_add i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne]
    · simp only [permMatrix_mul_apply, E, Matrix.map_apply, Matrix.of_apply, if_true,
        (Fin.castSucc_lt_last i).ne, if_false, map_one, map_neg, hq]
      have : σ (Fin.last n) = i0 := by simp [hσ]
      rw [this]
      field_simp
      ring
    · intro x hx
      simp [E, Matrix.map_apply, Ne.symm hx.1, hx.2]

def blockExt {n : ℕ} (k : Matrix (Fin n) (Fin n) V) : Matrix (Fin (n+1)) (Fin (n+1)) V :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks k 0 0 (1 : Matrix (Fin 1) (Fin 1) V))

lemma blockExt_det {n : ℕ} (k : Matrix (Fin n) (Fin n) V) : (blockExt V k).det = k.det := by
  simp [blockExt, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

lemma blockExt_cc {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (a b : Fin n) :
    blockExt V k a.castSucc b.castSucc = k a b := by
  simp [blockExt, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma blockExt_cl {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (a : Fin n) :
    blockExt V k a.castSucc (Fin.last n) = 0 := by
  simp [blockExt, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma blockExt_mul_apply {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (A : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (a : Fin n) (j : Fin (n+1)) :
    ((blockExt V k).map (algebraMap V F) * A) a.castSucc j =
      (k.map (algebraMap V F) * A.submatrix Fin.castSucc id) a j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.map_apply, blockExt_cc, blockExt_cl,
    map_zero, zero_mul, add_zero, Matrix.submatrix_apply, id]

theorem iwasawa_lowerTriangular (n : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧
      ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 := by
  induction n with
  | zero => exact ⟨1, by simp, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨P, hP, hPA⟩ := clear_last_column V F A
    set A' := P.map (algebraMap V F) * A with hA'
    obtain ⟨k', hk', hk'A⟩ := ih (A'.submatrix Fin.castSucc Fin.castSucc)
    refine ⟨blockExt V k' * P, ?_, fun i j hij => ?_⟩
    · rw [Matrix.det_mul, blockExt_det]
      exact hk'.mul hP
    · rw [Matrix.map_mul, Matrix.mul_assoc, ← hA']
      obtain ⟨a, rfl⟩ : ∃ a : Fin n, a.castSucc = i :=
        Fin.exists_castSucc_eq.mpr (ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j)))
      rw [blockExt_mul_apply]
      induction j using Fin.lastCases with
      | last =>
        rw [Matrix.mul_apply]
        simp only [Matrix.submatrix_apply, id, hPA, mul_zero, Finset.sum_const_zero]
      | cast b =>
        have := hk'A a b (Fin.castSucc_lt_castSucc_iff.mp hij)
        simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
end IwasawaLowerTri
end GlobalTheory

theorem GlobalTheory.iwasawa_lowerTriangular_of_det :
    ∀ (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 → ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧ ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 :=
  fun V F _ _ _ _ _ _ n A _ => GlobalTheory.IwasawaLowerTri.iwasawa_lowerTriangular V F n A
