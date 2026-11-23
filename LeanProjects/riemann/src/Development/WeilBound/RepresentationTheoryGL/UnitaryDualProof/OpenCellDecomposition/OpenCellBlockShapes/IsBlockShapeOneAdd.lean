import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.DistribHaarCharPi

open Matrix GlobalTheory.SmGL ValuativeRel
open scoped Pointwise

noncomputable section

namespace PositivityTheory.RgUd.CellB

variable {k : Type} [Field k]

variable {r m : ℕ}

def rowI (i : Fin m) : Fin (r + m) := ⟨i, by omega⟩

def colI (j : Fin r) : Fin (r + m) := ⟨m + j, by omega⟩

variable (r) in

def blockE (Y : Fin m × Fin r → k) : Matrix (Fin (r + m)) (Fin (r + m)) k := fun i j =>
  if h : (i : ℕ) < m ∧ m ≤ (j : ℕ) then Y (⟨i, h.1⟩, ⟨j - m, by omega⟩) else 0

theorem blockE_mul (Y Y' : Fin m × Fin r → k) : blockE r Y * blockE r Y' = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  unfold blockE
  by_cases hl : (l : ℕ) < m
  · have hl' : ¬ m ≤ (l : ℕ) := by omega
    simp [hl']
  · simp [hl]

theorem blockE_apply (Y : Fin m × Fin r → k) (i : Fin m) (j : Fin r) :
    blockE r Y (rowI i) (colI j) = Y (i, j) := by
  unfold blockE
  have hc : ((rowI (r := r) i : Fin (r + m)) : ℕ) < m ∧ m ≤ ((colI (m := m) j : Fin (r + m)) : ℕ) := by
    simp [rowI, colI]
  rw [dif_pos hc]
  congr 2
  all_goals
    apply Fin.ext
    simp [rowI, colI]

theorem one_rowI_colI (i : Fin m) (j : Fin r) : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) (rowI i) (colI j) = 0 := by
  rw [Matrix.one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp [rowI, colI] at this
  omega

def blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) : Fin m × Fin r → k := fun p => u (rowI p.1) (colI p.2)

def IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k) : Prop :=
  ∀ i j, u i j ≠ (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j → (i : ℕ) < m ∧ m ≤ (j : ℕ)

theorem eq_one_add_blockE {u : Matrix (Fin (r + m)) (Fin (r + m)) k} (hu : IsBlockShape u) :
    u = 1 + blockE r (blockY u) := by
  ext i j
  rw [Matrix.add_apply]
  unfold blockE
  by_cases hij : (i : ℕ) < m ∧ m ≤ (j : ℕ)
  · rw [dif_pos hij]
    have hne : i ≠ j := by
      intro h
      rw [h] at hij
      omega
    rw [Matrix.one_apply_ne hne, zero_add]
    show u i j = u (rowI _) (colI _)
    congr 1
    all_goals
      apply Fin.ext
      simp only [rowI, colI]
      try omega
  · rw [dif_neg hij, add_zero]
    by_contra h
    exact hij (hu i j h)

theorem isBlockShape_one_add (Y : Fin m × Fin r → k) : IsBlockShape (1 + blockE r Y) := by
  intro i j h
  rw [Matrix.add_apply] at h
  unfold blockE at h
  by_contra hc
  rw [dif_neg hc, add_zero] at h
  exact h rfl

def blockGL (Y : Fin m × Fin r → k) : GL (Fin (r + m)) k :=
  ⟨1 + blockE r Y, 1 - blockE r Y, by rw [add_mul, one_mul, mul_sub, mul_one, blockE_mul, sub_zero, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, blockE_mul, add_zero, add_sub_cancel_right]⟩

theorem blockGL_mem_unipB (Y : Fin m × Fin r → k) : blockGL Y ∈ unipB k (Fin (r + m)) := by
  rw [mem_unipB]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · show (1 + blockE r Y) i j = 0
    have hlt : (j : ℕ) < i := Fin.lt_iff_val_lt_val.mp hji
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji).symm, zero_add]
    unfold blockE
    rw [dif_neg (by omega)]
  · show (1 + blockE r Y) i i = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq]
    unfold blockE
    rw [dif_neg (by omega), add_zero]

def blockEquiv (U : Subgroup (GL (Fin (r + m)) k))
    (hU : ∀ u, u ∈ U ↔ u ∈ unipB k (Fin (r + m)) ∧ IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k)) :
    U ≃* Multiplicative (Fin m × Fin r → k) where
  toFun u := Multiplicative.ofAdd (blockY (u : GL (Fin (r + m)) k).1)
  invFun Y := ⟨blockGL (Multiplicative.toAdd Y), (hU _).2 ⟨blockGL_mem_unipB _, isBlockShape_one_add _⟩⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    show 1 + blockE r (blockY (u : GL (Fin (r + m)) k).1) = _
    exact (eq_one_add_blockE ((hU u.1).1 u.2).2).symm
  right_inv Y := by
    apply Multiplicative.toAdd.injective
    funext p
    show (1 + blockE r (Multiplicative.toAdd Y)) (rowI p.1) (colI p.2) = _
    rw [Matrix.add_apply, one_rowI_colI, zero_add, blockE_apply]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    funext p
    show ((u : GL (Fin (r + m)) k).1 * (v : GL (Fin (r + m)) k).1) (rowI p.1) (colI p.2) =
      (u : GL (Fin (r + m)) k).1 (rowI p.1) (colI p.2) + (v : GL (Fin (r + m)) k).1 (rowI p.1) (colI p.2)
    have hu := eq_one_add_blockE ((hU u.1).1 u.2).2
    have hv := eq_one_add_blockE ((hU v.1).1 v.2).2
    rw [hu, hv, add_mul, one_mul, mul_add, mul_one, blockE_mul, add_zero]
    simp only [Matrix.add_apply, one_rowI_colI, blockE_apply, zero_add]
    ring

theorem blockEquiv_apply (U : Subgroup (GL (Fin (r + m)) k))
    (hU : ∀ u, u ∈ U ↔ u ∈ unipB k (Fin (r + m)) ∧ IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k))
    (u : U) (i : Fin m) (j : Fin r) :
    Multiplicative.toAdd (blockEquiv U hU u) (i, j) = (u : GL (Fin (r + m)) k).1 (rowI i) (colI j) := rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (ι : Type) (γ : ValueGroupWithZero k) : AddSubgroup (ι → k) where
  carrier := {Y | ∀ i, valuation k (Y i) ≤ γ}
  add_mem' {a b} ha hb i := ((valuation k).map_add (a i) (b i)).trans (max_le (ha i) (hb i))
  zero_mem' i := by simp
  neg_mem' {a} ha i := by simpa using ha i

theorem mem_box {ι : Type} {γ : ValueGroupWithZero k} {Y : ι → k} : Y ∈ box ι γ ↔ ∀ i, valuation k (Y i) ≤ γ := Iff.rfl

theorem ball_eq_smul (c : kˣ) : {x : k | valuation k x ≤ valuation k (c : k)} = c • (𝒪[k] : Set k) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]
    simp
  have key : valuation k (((c⁻¹ : kˣ) : k) * x) = (valuation k (c : k))⁻¹ * valuation k x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  show valuation k x ≤ valuation k (c : k) ↔ valuation k (((c⁻¹ : kˣ) : k) * x) ≤ 1
  rw [key, inv_mul_le_iff₀ hc, mul_one]

theorem isCompact_box (ι : Type) [Fintype ι] (c : kˣ) : IsCompact (box ι (valuation k (c : k)) : Set (ι → k)) := by
  have hset : (box ι (valuation k (c : k)) : Set (ι → k)) =
      Set.univ.pi (fun _ => {x : k | valuation k x ≤ valuation k (c : k)}) := by
    ext Y
    simp [mem_box]
  rw [hset]
  exact isCompact_univ_pi (fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _)

theorem isOpen_box (ι : Type) [Fintype ι] (c : kˣ) : IsOpen (box ι (valuation k (c : k)) : Set (ι → k)) := by
  have hset : (box ι (valuation k (c : k)) : Set (ι → k)) =
      Set.univ.pi (fun _ => {x : k | valuation k x ≤ valuation k (c : k)}) := by
    ext Y
    simp [mem_box]
  have hball : IsOpen {x : k | valuation k x ≤ valuation k (c : k)} := by
    rw [ball_eq_smul]
    exact ((valuation k).isOpen_integer).smul c
  rw [hset]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => hball)

theorem smul_mem_box {ι : Type} {γ : ValueGroupWithZero k} (z : kˣ) (hz : valuation k (z : k) ≤ 1) {Y : ι → k}
    (hY : Y ∈ box ι γ) : z • Y ∈ box ι γ := by
  rw [mem_box] at hY ⊢
  intro i
  rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_mul]
  calc valuation k (z : k) * valuation k (Y i) ≤ 1 * γ := mul_le_mul' hz (hY i)
    _ = γ := one_mul γ

end PositivityTheory.RgUd.CellB
