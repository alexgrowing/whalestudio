import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne

namespace KStar.Selmer

open Matrix Module

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {n : Type*} [Fintype n] [DecidableEq n]

private theorem lengthDet_unit_mul {R : Type*} [CommRing R] (U A V : Matrix n n R)
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    Module.length R (H2 (U * A * V)) = Module.length R (H2 A) := by
  have hU' : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hU
  have hV' : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2 hV
  have hb : Function.Bijective U.mulVecLin :=
    ⟨Matrix.mulVec_injective_of_isUnit hU', Matrix.mulVec_surjective_iff_isUnit.2 hU'⟩
  have hs : LinearMap.range V.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.2 (Matrix.mulVec_surjective_iff_isUnit.2 hV')
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective U.mulVecLin hb) ?_)
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hs, Matrix.mulVecLin_mul,
    LinearMap.range_comp]
  rfl

private theorem lengthDet_diagonal {R : Type*} [CommRing R] (d : n → R) :
    Module.length R (H2 (diagonal d)) = ∑ i, Ring.ord R (d i) := by
  have h : LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i => (Ideal.span {d i} : Submodule R R)) := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
      true_imp_iff, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by rw [Matrix.mulVec_diagonal, mul_comm]⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, funext fun i => by rw [Matrix.mulVec_diagonal, mul_comm, hy]⟩
  rw [((Submodule.quotEquivOfEq _ _ h).trans (Submodule.quotientPi _)).length_eq,
    Module.length_pi_of_fintype]
  rfl

private theorem lengthDet_addVal_prod {ι : Type*} (s : Finset ι) (d : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, d i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]

theorem length_cokernel_eq_addVal_det (Φ : Matrix n n O) :
    Module.length O (H2 Φ) = IsDiscreteValuationRing.addVal O Φ.det := by
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  obtain ⟨U, V, d, hU, hV, h, -⟩ := exists_smith _ (Φ.submatrix e.symm e.symm)
  have hΦ : Φ = U.submatrix e e * diagonal (d ∘ e) * V.submatrix e e := by
    rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, ← h]
    ext i j
    simp
  have hU' : IsUnit (U.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  have hV' : IsUnit (V.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  rw [hΦ, lengthDet_unit_mul _ _ _ hU' hV', lengthDet_diagonal, Matrix.det_mul, Matrix.det_mul,
    IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hU',
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hV', zero_add, add_zero, Matrix.det_diagonal,
    lengthDet_addVal_prod]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal _

theorem specLength_eq_addVal {Λ : Type*} [CommRing Λ] (ψ : Λ →+* O) (Φ : Matrix n n Λ) :
    specLength ψ Φ = IsDiscreteValuationRing.addVal O (ψ Φ.det) := by
  rw [specLength, length_cokernel_eq_addVal_det, RingHom.map_det]
  rfl

end KStar.Selmer
