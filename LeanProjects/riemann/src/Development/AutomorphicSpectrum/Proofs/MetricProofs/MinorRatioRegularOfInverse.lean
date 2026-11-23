import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFact

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.UnitMinor

theorem det_mul_expand {K : Type*} [CommRing K] {a n : ℕ}
    (P : Matrix (Fin a) (Fin n) K) (Q : Matrix (Fin n) (Fin a) K) :
    (P * Q).det = ∑ J : Fin a → Fin n, (∏ l, P l (J l)) * (Q.submatrix J id).det :=
  _root_.Bl.general_b_fact.goal1 P Q

theorem mul_submatrix_castLE {Φ : Type*} [CommRing Φ] {n r a : ℕ} (ha : a ≤ r)
    (Fm : Matrix (Fin n) (Fin r) Φ) (U : Matrix (Fin r) (Fin r) Φ)
    (hU : U.BlockTriangular id) {m : Type*} (J : m → Fin n) :
    (Fm * U).submatrix J (Fin.castLE ha) =
      Fm.submatrix J (Fin.castLE ha) * U.submatrix (Fin.castLE ha) (Fin.castLE ha) := by
  ext x y
  have hinj : Function.Injective (Fin.castLE ha) := Fin.castLE_injective ha
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  have e : ∑ j, Fm.submatrix J (Fin.castLE ha) x j *
        U.submatrix (Fin.castLE ha) (Fin.castLE ha) j y =
      ∑ k ∈ Finset.univ.map ⟨Fin.castLE ha, hinj⟩,
        Fm (J x) k * U k (Fin.castLE ha y) := by
    rw [Finset.sum_map]
    rfl
  rw [e]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro k _ hk
  have hka : a ≤ k.val := by
    by_contra hlt
    push_neg at hlt
    exact hk (Finset.mem_map.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, by ext; simp⟩)
  have : U k (Fin.castLE ha y) = 0 := by
    apply hU
    show Fin.castLE ha y < k
    rw [Fin.lt_def]
    simp only [Fin.val_castLE]
    exact lt_of_lt_of_le y.isLt hka
  rw [this, mul_zero]

theorem det_castLE_triangular {Φ : Type*} [CommRing Φ] {r a : ℕ} (ha : a ≤ r)
    (U : Matrix (Fin r) (Fin r) Φ) (hU : U.BlockTriangular id) :
    (U.submatrix (Fin.castLE ha) (Fin.castLE ha)).det =
      ∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l) := by
  have : (U.submatrix (Fin.castLE ha) (Fin.castLE ha)).BlockTriangular id := by
    intro x y hxy
    apply hU
    show Fin.castLE ha y < Fin.castLE ha x
    show y.val < x.val
    exact hxy
  rw [Matrix.det_of_upperTriangular this]
  rfl

theorem det_mem_subring {Φ : Type*} [CommRing Φ] (R : Subring Φ) {a : ℕ}
    (M : Matrix (Fin a) (Fin a) Φ) (hM : ∀ i j, M i j ∈ R) : M.det ∈ R := by
  rw [Matrix.det_apply']
  refine R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => hM _ _)

theorem unit_minor : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (n r : ℕ) (Fm : Matrix (Fin n) (Fin r) Φ) (U : Matrix (Fin r) (Fin r) Φ) (C : Matrix (Fin r) (Fin n) Φ) (X : Φ), U.BlockTriangular id → (∀ a b, (Fm * U) a b / X ∈ R) → (∀ a b, C a b ∈ R) → (∀ a b, ∑ k, C a k * ((Fm * U) k b / X) = if a = b then 1 else 0) → ∀ (a : ℕ) (ha : a ≤ r) (J₀ : Fin a → Fin n), (Fm.submatrix J₀ (Fin.castLE ha)).det ≠ 0 → (∀ J : Fin a → Fin n, (Fm.submatrix J (Fin.castLE ha)).det / (Fm.submatrix J₀ (Fin.castLE ha)).det ∈ R) → (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ∈ R ∧ ((∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a)⁻¹ ∈ R ∧ (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ≠ 0 := by
  intro Φ _ R n r Fm U C X hU hB hC hCB a ha J₀ hD0 hratio
  set u : Φ := ∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l) with hu
  set D : (Fin a → Fin n) → Φ := fun J => (Fm.submatrix J (Fin.castLE ha)).det with hD
  set w : Φ := u * D J₀ / X ^ a with hw

  let B : Matrix (Fin n) (Fin r) Φ := X⁻¹ • (Fm * U)
  have hBent : ∀ k b, B k b = (Fm * U) k b / X := by
    intro k b
    simp [B, div_eq_inv_mul]
  have hminor : ∀ J : Fin a → Fin n,
      ((B.submatrix id (Fin.castLE ha)).submatrix J id).det = u * D J / X ^ a := by
    intro J
    have e : (B.submatrix id (Fin.castLE ha)).submatrix J id
        = X⁻¹ • (Fm.submatrix J (Fin.castLE ha) *
            U.submatrix (Fin.castLE ha) (Fin.castLE ha)) := by
      rw [← mul_submatrix_castLE ha Fm U hU J]
      ext x y
      simp [B]
    rw [e, Matrix.det_smul, Matrix.det_mul, det_castLE_triangular ha U hU]
    simp only [Fintype.card_fin, inv_pow, hD]
    rw [div_eq_inv_mul, mul_comm u]
  have hwR : w ∈ R := by
    have : w = ((B.submatrix id (Fin.castLE ha)).submatrix J₀ id).det := (hminor J₀).symm
    rw [this]
    refine det_mem_subring R _ fun i j => ?_
    simp only [Matrix.submatrix_apply, id]
    rw [hBent]
    exact hB _ _
  have hprod : (C.submatrix (Fin.castLE ha) id) * (B.submatrix id (Fin.castLE ha)) = 1 := by
    ext x y
    have e : ∀ j, (C.submatrix (Fin.castLE ha) id) x j * (B.submatrix id (Fin.castLE ha)) j y
        = C (Fin.castLE ha x) j * ((Fm * U) j (Fin.castLE ha y) / X) := fun j => by
      rw [← hBent]
      rfl
    rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_congr rfl (fun j _ => e j), hCB]
    simp only [(Fin.castLE_injective ha).eq_iff]
  set ρ : Φ := ∑ J : Fin a → Fin n, (∏ l, C (Fin.castLE ha l) (J l)) * (D J / D J₀) with hρ
  have hρR : ρ ∈ R :=
    R.sum_mem fun J _ => R.mul_mem (R.prod_mem fun l _ => hC _ _) (hratio J)
  have hone : w * ρ = 1 := by
    have h1 := det_mul_expand (C.submatrix (Fin.castLE ha) id) (B.submatrix id (Fin.castLE ha))
    rw [hprod, Matrix.det_one] at h1
    rw [h1, hρ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hminor J]
    simp only [Matrix.submatrix_apply, id]
    have hne : D J₀ ≠ 0 := hD0
    rw [hw]
    field_simp
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hone
  refine ⟨hwR, ?_, hw0⟩
  have : w⁻¹ = ρ := by
    rw [← mul_one w⁻¹, ← hone, inv_mul_cancel_left₀ hw0]
  rw [this]
  exact hρR

end GlobalTheory.CompanionTheory.Metric.UnitMinor
