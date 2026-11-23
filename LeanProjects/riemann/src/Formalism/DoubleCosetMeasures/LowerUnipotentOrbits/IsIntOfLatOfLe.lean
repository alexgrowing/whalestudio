import Formalism.DoubleCosetMeasures.Statement

set_option maxHeartbeats 400000

noncomputable section

open Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := by
  intro K _ n x y
  exact ⟨fun hx hy => isLowUni_mul K hx hy, fun hx hy => isUpUni_mul K hx hy,
    fun hx => ⟨isLowUni_inv K hx, isLowUni_det K hx⟩,
    fun hx => ⟨isUpUni_inv K hx, isUpUni_det K hx⟩⟩

section Simple

variable {K : Type} [CommRing K] {n : ℕ}

theorem low_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) (hy : IsLowUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) ⟨j.val + 1, h⟩ j = x ⟨j.val + 1, h⟩ j + y ⟨j.val + 1, h⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hy.2 j, hx.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : y k j = 0 := hy.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : x ⟨j.val + 1, h⟩ k = 0 := hx.1 (by simpa using hlt)
      simp [this]

theorem up_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) (hy : IsUpUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) j ⟨j.val + 1, h⟩ = x j ⟨j.val + 1, h⟩ + y j ⟨j.val + 1, h⟩ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hx.2 j, hy.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : x j k = 0 := hx.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : y k ⟨j.val + 1, h⟩ = 0 := hy.1 (by simpa using hlt)
      simp [this]

end Simple

theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := by
  intro K _ n x y
  constructor
  · intro hx hy
    unfold sLow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact low_simple_entry hx hy j h
    · simp [dif_neg h]
  · intro hx hy
    unfold sUp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact up_simple_entry hx hy j h
    · simp [dif_neg h]

section Int

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem isInt_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hB : IsInt R B) :
    IsInt R (A * B) := by
  intro a b
  rw [Matrix.mul_apply]
  exact R.sum_mem fun k _ => R.mul_mem (hA a k) (hB k b)

theorem isInt_adjugate {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) :
    IsInt R A.adjugate := by
  let A' : Matrix (Fin n) (Fin n) R := fun a b => ⟨A a b, hA a b⟩
  have hmap : R.subtype.mapMatrix A' = A := by ext a b; rfl
  intro a b
  rw [← hmap, ← RingHom.map_adjugate]
  exact (A'.adjugate a b).2

theorem isInt_inv {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hd : A.det = 1) :
    IsInt R A⁻¹ := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  exact isInt_adjugate R hA

end Int

theorem intInv : Formalism.DoubleCosetMeasures.IntInv := by
  intro K _ R n a b Z ha hb haR hbR
  have hda : IsUnit a.det := by simp [isLowUni_det K ha]
  have hdb : IsUnit b.det := by simp [isUpUni_det K hb]
  constructor
  · intro h
    have hZ : Z = a⁻¹ * (a * Z * b) * b⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv b hdb, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]
    rw [hZ]
    exact isInt_mul R (isInt_mul R (isInt_inv R haR (isLowUni_det K ha)) h)
      (isInt_inv R hbR (isUpUni_det K hb))
  · intro h
    exact isInt_mul R (isInt_mul R haR h) hbR

section Lat

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem mem_latOf (g : GL (Fin n) K) (w : Fin n → K) :
    w ∈ latOf R g ↔ ∃ v : Fin n → R, (g : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (v j : K)) = w := by
  unfold latOf
  simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  rfl

theorem latOf_le (g h : GL (Fin n) K)
    (hM : IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) :
    latOf R h ≤ latOf R g := by
  intro w hw
  obtain ⟨v, rfl⟩ := (mem_latOf R h w).1 hw
  rw [mem_latOf]
  set M : Matrix (Fin n) (Fin n) K := ((g⁻¹ * h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  refine ⟨fun i => ⟨(M *ᵥ (fun j => (v j : K))) i, ?_⟩, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact R.sum_mem fun k _ => R.mul_mem (hM i k) (v k).2
  · have hgM : (g : Matrix (Fin n) (Fin n) K) * M = h := by
      rw [hMdef, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ (M *ᵥ (fun j => (v j : K))) = _
    rw [Matrix.mulVec_mulVec, hgM]

theorem isInt_of_latOf_le (g h : GL (Fin n) K) (hle : latOf R h ≤ latOf R g) :
    IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  intro i j
  have hmem : (h : Matrix (Fin n) (Fin n) K) *ᵥ (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K))
      ∈ latOf R h := (mem_latOf R h _).2 ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := (mem_latOf R g _).1 (hle hmem)
  have hcoe : (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K)) = Pi.single j (1 : K) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hcoe] at hv
  have key : (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K) =
      fun k => (v k : K) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have := congrFun key i
  rw [Matrix.mulVec_single_one] at this
  simp only [Matrix.col_apply] at this
  rw [this]
  exact (v i).2

end Lat

theorem latticeCoset : Formalism.DoubleCosetMeasures.LatticeCoset := by
  intro K _ R n g h
  constructor
  · intro e
    exact ⟨isInt_of_latOf_le R g h (le_of_eq e.symm), isInt_of_latOf_le R h g (le_of_eq e)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (latOf_le R h g h2) (latOf_le R g h h1)

end Formalism.DoubleCosetMeasures.P
