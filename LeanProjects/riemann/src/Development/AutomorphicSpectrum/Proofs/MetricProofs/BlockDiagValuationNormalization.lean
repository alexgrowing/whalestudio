import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.IwBlock

theorem exists_blocks_add {L : Type} [Field L] (V : ValuationSubring L) (n m : ℕ)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) L)
    (hA : ∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin (n + m)) (Fin (n + m)) V) (U : Matrix (Fin (n + m)) (Fin (n + m)) L),
      IsUnit K.det ∧ (∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let A₁ : Matrix (Fin n) (Fin n) L := fun i k => A (e (Sum.inl i)) (e (Sum.inl k))
  let A₂ : Matrix (Fin m) (Fin m) L := fun i k => A (e (Sum.inr i)) (e (Sum.inr k))
  have lt_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have ge_r : ∀ i : Fin m, ¬ ((e (Sum.inr i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have val_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) = i := fun i => by simp [e]
  have val_r : ∀ i : Fin m, ((e (Sum.inr i) : Fin (n + m)) : ℕ) = n + i := fun i => by simp [e]
  have hB : A.submatrix e e = fromBlocks A₁ 0 0 A₂ := by
    ext (i | i) (k | k)
    · rfl
    · exact hA _ _ fun h => ge_r k (h.1 (lt_l i))
    · exact hA _ _ fun h => ge_r i (h.2 (lt_l k))
    · rfl
  have hdet : A₁.det * A₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ A₁ 0 A₂, ← hB, det_submatrix_equiv_self]
    exact hd
  obtain ⟨k₁, U₁, hk₁, hU₁, hd₁, e₁⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₁ (left_ne_zero_of_mul hdet)
  obtain ⟨k₂, U₂, hk₂, hU₂, hd₂, e₂⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₂ (right_ne_zero_of_mul hdet)
  refine ⟨(fromBlocks k₁ 0 0 k₂).submatrix e.symm e.symm, (fromBlocks U₁ 0 0 U₂).submatrix e.symm e.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact hk₁.mul hk₂
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rcases x with i | i <;> rcases y with k | k
    · exact absurd (iff_of_true (lt_l i) (lt_l k)) h
    · simp
    · simp
    · exact absurd (iff_of_false (ge_r i) (ge_r k)) h
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have h' : ((e y : Fin (n + m)) : ℕ) < (e x : Fin (n + m)) := h
    rcases x with i | i <;> rcases y with k | k
    · rw [val_l, val_l] at h'
      simpa using hU₁ (show k < i from h')
    · simp
    · simp
    · rw [val_r, val_r] at h'
      simpa using hU₂ (show k < i from Nat.lt_of_add_lt_add_left h')
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    rcases x with i | i
    · simpa using hd₁ i
    · simpa using hd₂ i
  · have h1 : A = (fromBlocks A₁ 0 0 A₂).submatrix e.symm e.symm := by
      rw [← hB]; ext a b; simp
    have h3 : fromBlocks A₁ 0 0 A₂ =
        (fromBlocks k₁ 0 0 k₂).map (algebraMap V L) * fromBlocks U₁ 0 0 U₂ := by
      rw [fromBlocks_map, fromBlocks_multiply, ← e₁, ← e₂,
        Matrix.map_zero _ (map_zero (algebraMap V L)), Matrix.map_zero _ (map_zero (algebraMap V L))]
      simp
    rw [h1, h3, ← submatrix_mul_equiv _ _ _ e.symm _]
    rfl

theorem exists_blocks {L : Type} [Field L] (V : ValuationSubring L) (N n : ℕ) (hn : n ≤ N)
    (A : Matrix (Fin N) (Fin N) L)
    (hA : ∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin N) (Fin N) V) (U : Matrix (Fin N) (Fin N) L),
      IsUnit K.det ∧ (∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact exists_blocks_add V n m A hA hd

theorem inv_diag_ne_zero {L : Type} [Field L] {N : ℕ} {U : Matrix (Fin N) (Fin N) L}
    (hU : U.BlockTriangular id) (hd : IsUnit U.det) (a : Fin N) : U⁻¹ a a ≠ 0 := by
  have hI : U⁻¹.BlockTriangular id := by
    letI := Matrix.invertibleOfIsUnitDet U hd
    exact blockTriangular_inv_of_blockTriangular hU
  intro e
  have h := congrFun (congrFun (nonsing_inv_mul U hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a (fun c _ hc => ?_) (by simp), e,
    zero_mul] at h
  · exact zero_ne_one h
  · rcases lt_or_gt_of_ne hc with l | l
    · rw [hI l, zero_mul]
    · rw [hU l, mul_zero]

theorem main : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (A : Matrix (Fin N) (Fin N) L), IsBlockDiag j A → A.det ≠ 0 → ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ (∀ a c, (A * b) a c ∈ V) ∧ (A * b).det ≠ 0 ∧ ((A * b).det)⁻¹ ∈ V := by
  intro L _ V N j A hA hd
  obtain ⟨K, U, hK, hUb, hUt, hUd, hAe⟩ := exists_blocks V N (N - j) (Nat.sub_le N j) A hA hd
  have hUdet : IsUnit U.det := by
    rw [det_of_upperTriangular hUt]
    exact (Finset.prod_ne_zero_iff.2 fun a _ => hUd a).isUnit
  have hAU : A * U⁻¹ = K.map (algebraMap V L) := by
    rw [hAe, Matrix.mul_nonsing_inv_cancel_right _ _ hUdet]
  have hKdet : (K.map (algebraMap V L)).det = algebraMap V L K.det := (RingHom.map_det _ K).symm
  have hUb' : IsBlockDiag j U := hUb
  refine ⟨U⁻¹, hUb'.inv hUdet, ?_, inv_diag_ne_zero hUt hUdet, fun a c => ?_, ?_, ?_⟩
  · letI := Matrix.invertibleOfIsUnitDet U hUdet
    exact blockTriangular_inv_of_blockTriangular hUt
  · rw [hAU]
    exact (K a c).2
  · rw [hAU, hKdet]
    exact (hK.map (algebraMap V L)).ne_zero
  · rw [hAU, hKdet]
    obtain ⟨u, hu⟩ := hK
    rw [← hu]
    have e : (algebraMap V L (u : V))⁻¹ = algebraMap V L ((u⁻¹ : Vˣ) : V) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e]
    exact ((u⁻¹ : Vˣ) : V).2

end GlobalTheory.CompanionTheory.Ar.PB.IwBlock
