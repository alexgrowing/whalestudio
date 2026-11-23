import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
namespace GlobalTheory.ParahoricTranslate

theorem isUnit_det_one_add_nonunit_smul {O : Type} [CommRing O] [IsLocalRing O] {r : ℕ} (ϖ : O)
    (hϖ : ¬ IsUnit ϖ) (Z : Matrix (Fin r) (Fin r) O) :
    IsUnit (1 + ϖ • Z).det := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h
  set f := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
  have h0 : f (1 + ϖ • Z).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hf : f ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ))
  have h1 : f.mapMatrix (1 + ϖ • Z) = 1 := by
    rw [map_add, map_one]
    ext i j
    simp [hf]
  rw [RingHom.map_det, h1, Matrix.det_one] at h0
  exact one_ne_zero h0

theorem toRows_left_mul_matrix_eq {K : Type} [CommRing K] {r t : ℕ}
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : Matrix (Fin r) (Fin r) K) :
    Matrix.toRows₁ (x * g) = Matrix.toRows₁ x * g := by
  ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hirr x g g' z z' hx hx' y w hy
  set φ := algebraMap O K
  set e := Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)
  set Z := Matrix.toRows₁ z
  set Z' := Matrix.toRows₁ z'
  set P : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z
  set P' : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z'
  set A := Matrix.toRows₁ x
  have hP : IsUnit P.det := isUnit_det_one_add_nonunit_smul ϖ hirr.not_isUnit Z
  have hA : A * (g : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P := by
    have := congrArg Matrix.toRows₁ hx
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z)).map φ = (1 + ϖ • Z).map φ
    congr 1
  have hA' : A * (g' : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P' := by
    have := congrArg Matrix.toRows₁ hx'
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z')).map φ = (1 + ϖ • Z').map φ
    congr 1
  have hPK : IsUnit (φ.mapMatrix P).det := by
    rw [← RingHom.map_det]; exact hP.map φ
  have hAu : IsUnit A.det := by
    rw [← hA, Matrix.det_mul] at hPK
    exact isUnit_of_mul_isUnit_left hPK
  set c : Matrix (Fin r) (Fin r) O := P⁻¹ * P'
  have hgc : (g' : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c := by
    have h2 : A * (g' : Matrix (Fin r) (Fin r) K) = A * ((g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c) := by
      rw [hA', ← Matrix.mul_assoc, hA, map_mul, ← Matrix.mul_assoc, ← map_mul,
        Matrix.mul_nonsing_inv _ hP, map_one, Matrix.one_mul]
    have h3 := congrArg (fun M => A⁻¹ * M) h2
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hAu] using h3
  refine ⟨Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c, ?_⟩
  have hc : c = 1 + ϖ • (P⁻¹ * (Z' - Z)) := by
    have : P' = P + ϖ • (Z' - Z) := by
      simp only [P, P', smul_sub]; abel
    simp only [c, this, Matrix.mul_add, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hP]
  have key : (e + ϖ • w) * c = e + ϖ • (Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c) := by
    rw [Matrix.add_mul, Matrix.smul_mul]
    have he : e * c = Matrix.fromRows c (0 : Matrix (Fin t) (Fin r) O) := by
      simp [e, Matrix.fromRows_mul]
    rw [he]
    nth_rewrite 1 [hc]
    ext (i | i) j <;> simp [e, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, smul_add, add_assoc]
  rw [hgc, ← Matrix.mul_assoc, hy, RingHom.mapMatrix_apply, ← Matrix.map_mul, key]

end GlobalTheory.ParahoricTranslate
