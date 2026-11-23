import Mathlib

open Module Submodule Function

namespace GlobalTheory

namespace MaximalMinor

section Cramer

variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]

theorem det_smul_eq_sum_det_update (b : Basis ι R F) (v : ι → F) (x : F) :
    b.det v • x = ∑ i, b.det (update v i x) • v i := by
  apply b.equivFun.injective
  have h := Matrix.mulVec_cramer (b.toMatrix v) (b.equivFun x)
  rw [map_smul, Basis.det_apply, ← h]
  ext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Basis.equivFun_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.cramer_apply, Basis.det_apply,
    Basis.toMatrix_update, Basis.toMatrix_apply, mul_comm]

theorem det_ne_zero_of_linearIndependent [IsDomain R] (b : Basis ι R F) {v : ι → F}
    (hv : LinearIndependent R v) : b.det v ≠ 0 := by
  intro h
  rw [Basis.det_apply] at h
  obtain ⟨c, hc, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine hc (funext (Fintype.linearIndependent_iff.1 hv c ?_))
  apply b.equivFun.injective
  ext j
  simpa [Matrix.mulVec, dotProduct, Basis.toMatrix_apply, mul_comm] using congrFun h0 j

theorem mem_span_of_det_update_mem (b : Basis ι R F) {v : ι → F}
    (hv : b.det v ∈ nonZeroDivisors R) {x : F}
    (hx : ∀ i, b.det (update v i x) ∈ span A {b.det v}) : x ∈ span A (Set.range v) := by
  choose a ha using fun i => mem_span_singleton.1 (hx i)
  refine (mem_span_range_iff_exists_fun A).2 ⟨a, ?_⟩
  have h1 : b.det v • (∑ i, a i • v i) = b.det v • x := by
    rw [det_smul_eq_sum_det_update b v x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, smul_assoc, ← algebraMap_smul R (a i), ← algebraMap_smul R (a i), smul_comm]
  apply b.equivFun.injective
  ext j
  have h2 := congrArg (fun y => b.equivFun y j) h1
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_cancel_left_mem_nonZeroDivisors hv).1 h2

theorem span_range_comp_eq (b : Basis ι R F) (G : κ → F) {σ : ι → κ}
    (hσ : b.det (G ∘ σ) ∈ nonZeroDivisors R)
    (h : ∀ τ : ι → κ, b.det (G ∘ τ) ∈ span A {b.det (G ∘ σ)}) :
    span A (Set.range (G ∘ σ)) = span A (Set.range G) := by
  refine le_antisymm (span_mono (Set.range_comp_subset_range _ _)) (span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine mem_span_of_det_update_mem b hσ fun i => ?_
  rw [← comp_update]
  exact h _

theorem exists_det_ne_zero [IsDomain R] (b : Basis ι R F) (G : κ → F)
    (hr : Fintype.card ι ≤ finrank R (span R (Set.range G))) :
    ∃ σ : ι → κ, b.det (G ∘ σ) ≠ 0 := by
  by_contra! h
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank hr
  have hw' := (hw.comp _ (Fintype.equivFin ι).injective).map' _ (ker_subtype _)
  refine det_ne_zero_of_linearIndependent b hw' ?_
  have h0 : (b.det.compLinearMap (span R (Set.range G)).subtype).toMultilinearMap = 0 := by
    refine MultilinearMap.ext_of_span_eq_top
      (g := fun (_ : ι) (k : κ) => (⟨G k, subset_span ⟨k, rfl⟩⟩ : span R (Set.range G)))
      (fun _ => span_range_subtype_eq_top_iff _ _ |>.2 rfl) fun σ => h σ
  exact DFunLike.congr_fun h0 (w ∘ Fintype.equivFin ι)

end Cramer

end MaximalMinor

end GlobalTheory
