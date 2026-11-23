import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviVReLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.KappaStatementHolds

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

variable {r : ℕ}

theorem sum_eq_castLE {m : ℕ} (hm : m ≤ r) {M : Type} [AddCommMonoid M] (g : Fin r → M)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → g k = 0) :
    ∑ k, g k = ∑ j : Fin m, g (Fin.castLE hm j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ g
    (fun k hk => hg k ?_) (fun j => rfl)
  by_contra h
  push_neg at h
  exact hk ⟨⟨k, h⟩, Fin.ext rfl⟩

theorem sub_LMU {m : ℕ} (hm : m ≤ r) (L M U : Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ a c : Fin r, c < a → L a c = 0) (hU : ∀ a c : Fin r, c < a → U a c = 0) :
    (Lᵀ * M * U).submatrix (Fin.castLE hm) (Fin.castLE hm) =
      (L.submatrix (Fin.castLE hm) (Fin.castLE hm))ᵀ * M.submatrix (Fin.castLE hm) (Fin.castLE hm) *
        U.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext i j
  simp only [submatrix_apply, mul_apply, transpose_apply]
  rw [sum_eq_castLE hm (fun b => (∑ a, L a (Fin.castLE hm i) * M a b) * U b (Fin.castLE hm j))]
  · refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [sum_eq_castLE hm (fun a => L a (Fin.castLE hm i) * M a (Fin.castLE hm b))]
    intro k hk
    have := i.isLt
    rw [hL k _ (by simp only [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]
  · intro k hk
    have := j.isLt
    rw [hU k _ (by simp only [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

theorem lminor_LMU (L M U : Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ a c : Fin r, c < a → L a c = 0) (hU : ∀ a c : Fin r, c < a → U a c = 0) (k : Fin (r + 1)) :
    lminor (Lᵀ * M * U) k =
      (L.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        lminor M k *
        (U.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  unfold lminor
  rw [sub_LMU _ L M U hL hU, det_mul, det_mul, det_transpose]

theorem lminor_map_conj (M : Matrix (Fin r) (Fin r) ℂ) (k : Fin (r + 1)) :
    lminor (M.map (starRingEnd ℂ)) k = starRingEnd ℂ (lminor M k) := by
  unfold lminor
  rw [RingHom.map_det]
  rfl

theorem tr_D_conj (A : Matrix (Fin r) (Fin r) ℂ) (D : Fin r → ℝ) :
    Aᵀ * (diagonal fun k => (D k : ℂ)) * A.map (starRingEnd ℂ) =
      (Aᴴ * (diagonal fun k => (D k : ℂ)) * A).map (starRingEnd ℂ) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
