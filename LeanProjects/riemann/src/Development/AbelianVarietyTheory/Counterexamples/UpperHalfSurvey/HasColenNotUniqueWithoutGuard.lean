import Mathlib
import ReciprocityTheory.DualLattices.CharTableIsUnit

noncomputable section

namespace GlobalTheory.HopfOrderCheck

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem vdet_le_of_span_le (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det ≤ v B'.det := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => B' x i) = fun x => B x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  have hB : B = B' * (Matrix.of fun i j => c j i).map (algebraMap R C) := by
    ext x j
    have := congrFun (hc j) x
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hd : ((Matrix.of fun i j => c j i).map (algebraMap R C)).det
      = algebraMap R C (Matrix.of fun i j => c j i).det := ((algebraMap R C).map_det _).symm
  rw [hB, Matrix.det_mul, map_mul, hd]
  exact mul_le_of_le_one_right' (hv _)

theorem hasColen_unique (v : Valuation C NNReal) (hv : ∀ r : R, v (algebraMap R C r) ≤ 1)
    {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)} {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M c') : c = c' := by
  obtain ⟨B, hB, rfl⟩ := h
  obtain ⟨B', hB', rfl⟩ := h'
  exact le_antisymm (vdet_le_of_span_le v hv B B' (by rw [← hB, ← hB']))
    (vdet_le_of_span_le v hv B' B (by rw [← hB, ← hB']))

theorem intFun_eq_span {X : Type} [Fintype X] [DecidableEq X] :
    intFun (C := C) R X = Submodule.span R (Set.range fun j x => (1 : Matrix X X C) x j) := by
  apply le_antisymm
  · intro f hf
    choose r hr using hf
    refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨r, ?_⟩
    ext x
    simp [Finset.sum_apply, Algebra.smul_def, Matrix.one_apply, hr]
  · refine Submodule.span_le.mpr ?_
    rintro f ⟨j, rfl⟩ x
    by_cases h : x = j
    · exact ⟨1, by simp [Matrix.one_apply, h]⟩
    · exact ⟨0, by simp [Matrix.one_apply, h]⟩

theorem hasColen_intFun (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X] :
    HasColen R v (intFun (C := C) R X) 1 := ⟨1, intFun_eq_span, by simp⟩

theorem hasColen_not_unique_without_guard (v : Valuation C NNReal) (t : C) (ht : t ≠ 0) :
    HasColen C v (⊤ : Submodule C (Unit → C)) (v t) := by
  refine ⟨Matrix.of fun _ _ => t, ?_, by simp⟩
  symm
  rw [eq_top_iff]
  intro f _
  refine (Submodule.mem_span_range_iff_exists_fun C).mpr ⟨fun _ => f () / t, ?_⟩
  ext x
  simp [ht]

end GlobalTheory.HopfOrderCheck
