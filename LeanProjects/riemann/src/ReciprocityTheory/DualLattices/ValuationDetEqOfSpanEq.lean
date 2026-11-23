import ReciprocityTheory.DualLattices.TensorSpan

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]

theorem mem_spanCols_iff (B : Matrix X X C) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ ∃ w ∈ intFun (C := C) R X, f = B *ᵥ w := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => algebraMap R C (c j), fun j => ⟨c j, rfl⟩, ?_⟩
    ext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    choose c hc using hw
    refine ⟨c, ?_⟩
    ext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, hc, mul_comm]

theorem mem_spanCols_iff_inv (B : Matrix X X C) (hB : IsUnit B.det) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ B⁻¹ *ᵥ f ∈ intFun (C := C) R X := by
  rw [mem_spanCols_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  · intro h
    exact ⟨_, h, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]⟩

theorem mem_dualLat_spanCols_iff (B : Matrix X X C) (u : X → C) :
    u ∈ dualLat (Submodule.span R (Set.range fun j x => B x j)) ↔ u ᵥ* B ∈ intFun (C := C) R X := by
  constructor
  · intro h j
    obtain ⟨r, hr⟩ := h _ (Submodule.subset_span ⟨j, rfl⟩)
    exact ⟨r, by rw [hr]; simp [Matrix.vecMul, dotProduct]⟩
  · intro h f hf
    obtain ⟨w, hw, rfl⟩ := (mem_spanCols_iff B f).1 hf
    choose r hr using h
    choose s hs using hw
    refine ⟨∑ j, r j * s j, ?_⟩
    simp only [map_sum, map_mul, hr, hs, Matrix.vecMul, dotProduct, Matrix.mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem dualLat_spanCols (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (Submodule.span R (Set.range fun j x => B x j)) =
      Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
  have hBT : IsUnit (B⁻¹)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ hB
  ext u
  rw [mem_dualLat_spanCols_iff, mem_spanCols_iff_inv _ hBT, ← Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.mulVec_transpose]

theorem dualLat_dualLat_spanCols (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (dualLat (Submodule.span R (Set.range fun j x => B x j))) =
      Submodule.span R (Set.range fun j x => B x j) := by
  have hBT : IsUnit (B⁻¹)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ hB
  rw [dualLat_spanCols B hB, dualLat_spanCols _ hBT, ← Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.transpose_transpose]

theorem valuation_det_le_one (v : Valuation C NNReal) (hv : v.Integers R) (P : Matrix X X C)
    (hP : ∀ x j, ∃ r : R, algebraMap R C r = P x j) : v P.det ≤ 1 := by
  choose r hr using hP
  have : P = (Matrix.of r).map (algebraMap R C) := by ext x j; simp [hr]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hv.map_le_one _

theorem valuation_det_eq_of_span_eq (v : Valuation C NNReal) (hv : v.Integers R)
    (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det = v B'.det := by
  have key : ∀ (B B' : Matrix X X C),
      Submodule.span R (Set.range fun j x => B x j) ≤
        Submodule.span R (Set.range fun j x => B' x j) → v B.det ≤ v B'.det := by
    intro B B' hle
    have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
      (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
    choose w hw hBw using hcol
    have hBP : B = B' * Matrix.of fun x j => w j x := by
      ext x j
      have := congrFun (hBw j) x
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hle1 : v (Matrix.of fun x j => w j x).det ≤ 1 :=
      valuation_det_le_one v hv _ fun x j => hw j x
    rw [hBP, Matrix.det_mul, map_mul]
    exact mul_le_of_le_one_right' hle1
  exact le_antisymm (key B B' h.le) (key B' B h.ge)

end ReciprocityTheory.PGsh.L2
