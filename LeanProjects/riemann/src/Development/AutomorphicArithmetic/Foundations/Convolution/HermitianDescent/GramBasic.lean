import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem exists_diag {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (hG : G.charpoly.Separable) :
    ∃ (l : Fin n → K) (x : GL (Fin n) K), Function.Injective l ∧ G * x.val = x.val * diagonal l := by
  classical
  have hsp : G.charpoly.Splits := IsAlgClosed.splits _
  have hcard : G.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hG), ← hsp.natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := G.charpoly.roots.toFinset.equivFinOfCardEq hcard
  obtain ⟨x, hx⟩ := (conjSep K K n G hG).1 (diagonal fun i => (e.symm i : K)) (by
    rw [Matrix.charpoly_diagonal, e.symm.prod_comp (fun a => (X - C (a : K))),
      Finset.prod_coe_sort _ (fun a : K => X - C a)]
    conv_rhs => rw [hsp.eq_prod_roots_of_monic G.charpoly_monic]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_roots hG).dedup])
  exact ⟨_, x, Subtype.val_injective.comp e.symm.injective, hx⟩

private theorem unit_of_closed {R : Type} [CommRing R] (r : R)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K), φ r ≠ 0) : IsUnit r := by
  by_contra hr
  obtain ⟨m, hm, hrm⟩ := exists_max_ideal_of_mem_nonunits hr
  letI := Ideal.Quotient.field m
  refine h (AlgebraicClosure (R ⧸ m)) ((algebraMap (R ⧸ m) _).comp (Ideal.Quotient.mk m)) ?_
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hrm, map_zero]

section

variable {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {n : ℕ} (B : Module.Basis (Fin n) R L)

private theorem units_of_sep (g : L) (hg : (Algebra.leftMulMatrix B g).charpoly.Separable) :
    IsUnit (Matrix.of fun i j => Algebra.trace R L (B i * B j)).det ∧
      IsUnit (Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i).det := by
  suffices H : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K),
      φ (Matrix.of fun i j => Algebra.trace R L (B i * B j)).det ≠ 0 ∧
      φ (Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i).det ≠ 0 from
    ⟨unit_of_closed _ fun K _ _ φ => (H K φ).1, unit_of_closed _ fun K _ _ φ => (H K φ).2⟩
  intro K _ _ φ
  let ρ : L →+* Matrix (Fin n) (Fin n) K := φ.mapMatrix.comp (Algebra.leftMulMatrix B).toRingHom
  have hρ : ∀ z, ρ z = (Algebra.leftMulMatrix B z).map φ := fun _ => rfl
  obtain ⟨l, x, hl, hx⟩ := exists_diag (ρ g) (by rw [hρ, Matrix.charpoly_map]; exact hg.map)
  let τ : L → Matrix (Fin n) (Fin n) K := fun z => (x⁻¹).val * ρ z * x.val
  have hτmul : ∀ z w, τ (z * w) = τ z * τ w := fun z w => by
    simp only [τ, map_mul, mul_assoc, Units.mul_inv_cancel_left]
  have hτg : τ g = diagonal l := by
    simp only [τ, mul_assoc, hx, Units.inv_mul_cancel_left]
  have hd : ∀ z, τ z = diagonal fun i => τ z i i := fun z => by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · have h := congrFun (congrFun (show τ z * diagonal l = diagonal l * τ z by
        rw [← hτg, ← hτmul, ← hτmul, mul_comm]) i) j
      rw [mul_diagonal, diagonal_mul, mul_comm (l i)] at h
      rw [diagonal_apply_ne _ hij]
      by_contra h0
      exact hij (hl (mul_left_cancel₀ h0 h)).symm
  have hpow : ∀ j : ℕ, τ (g ^ j) = diagonal fun i => l i ^ j := fun j => by
    induction j with
    | zero => simp [τ]
    | succ j ih => rw [pow_succ, hτmul, ih, hτg, diagonal_mul_diagonal]; simp [pow_succ]
  let w : Fin n → K := (x⁻¹).val *ᵥ fun i => φ (B.repr 1 i)
  have hw : ∀ z i, ((x⁻¹).val *ᵥ fun i => φ (B.repr z i)) i = w i * τ z i i := fun z i => by
    have h1 : (fun i => φ (B.repr z i)) = ρ z *ᵥ fun i => φ (B.repr 1 i) := by
      funext i
      have := congrFun (Algebra.leftMulMatrix_mulVec_repr B z 1) i
      rw [mul_one] at this
      rw [← this, hρ, RingHom.map_mulVec]; rfl
    have h2 : (x⁻¹).val * ρ z = τ z * (x⁻¹).val := by
      simp only [τ, Units.mul_inv_cancel_right]
    rw [h1, mulVec_mulVec, h2, ← mulVec_mulVec, hd z, mulVec_diagonal, mul_comm]
    simp [w]
  have hxd : (x⁻¹).val.det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (x⁻¹).isUnit).ne_zero
  have hE : (x⁻¹).val = diagonal w * Matrix.of fun i j => τ (B j) i i := by
    ext i j
    rw [diagonal_mul, of_apply, ← hw]
    simp [mulVec, dotProduct, Finsupp.single_apply, apply_ite φ]
  rw [hE, det_mul] at hxd
  constructor
  · have : (Matrix.of fun i j => Algebra.trace R L (B i * B j)).map φ =
        (Matrix.of fun i j => τ (B j) i i)ᵀ * Matrix.of fun i j => τ (B j) i i := by
      ext i j
      have h1 : (τ (B i * B j)).trace = (ρ (B i * B j)).trace := by
        simp only [τ]
        rw [trace_mul_comm, Units.mul_inv_cancel_left]
      rw [map_apply, of_apply, Algebra.trace_eq_matrix_trace B, AddMonoidHom.map_trace, ← hρ, ← h1,
        hτmul, hd (B i), hd (B j), diagonal_mul_diagonal, trace_diagonal]
      simp [Matrix.mul_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, this, det_mul, det_transpose]
    exact mul_ne_zero (right_ne_zero_of_mul hxd) (right_ne_zero_of_mul hxd)
  · have : (x⁻¹).val * (Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i).map φ =
        diagonal w * vandermonde l := by
      ext i j
      rw [diagonal_mul, vandermonde_apply]
      have := hw (g ^ (j : ℕ)) i
      rw [hpow, diagonal_apply_eq] at this
      rw [← this]; rfl
    have h2 := congrArg det this
    rw [det_mul, det_mul] at h2
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact right_ne_zero_of_mul (h2 ▸ mul_ne_zero (left_ne_zero_of_mul hxd)
      (det_vandermonde_ne_zero_iff.2 hl))

private theorem comm_of_sep (g : L) (hg : (Algebra.leftMulMatrix B g).charpoly.Separable)
    (y : Matrix (Fin n) (Fin n) R) (hy : y * Algebra.leftMulMatrix B g = Algebra.leftMulMatrix B g * y) :
    ∃ z, y = Algebra.leftMulMatrix B z := by
  refine ⟨B.equivFun.symm (y *ᵥ B.repr 1), ?_⟩
  refine ((isUnit_iff_isUnit_det _).2 (units_of_sep B g hg).2).mul_right_cancel ?_
  ext i j
  have h1 : ∀ M : Matrix (Fin n) (Fin n) R,
      (M * Matrix.of fun i j : Fin n => B.repr (g ^ (j : ℕ)) i) i j = (M *ᵥ B.repr (g ^ (j : ℕ))) i :=
    fun M => rfl
  have h2 : y * Algebra.leftMulMatrix B (g ^ (j : ℕ)) = Algebra.leftMulMatrix B (g ^ (j : ℕ)) * y := by
    rw [map_pow]; exact (Commute.pow_right hy _).eq
  rw [h1, h1, Algebra.leftMulMatrix_mulVec_repr, mul_comm, ← Algebra.leftMulMatrix_mulVec_repr,
    ← mul_one (g ^ (j : ℕ)), ← Algebra.leftMulMatrix_mulVec_repr, mul_one, mulVec_mulVec, h2,
    ← mulVec_mulVec]
  congr 1
  exact (B.equivFun.apply_symm_apply _).symm

end

section

variable {k R A : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing A] [Algebra k A] {n : ℕ}
  (b : Module.Basis (Fin n) k A)

private theorem gramL_apply (s : R ⊗[k] A) (i j : Fin n) : gramL b s i j =
    Algebra.trace R _ (s * (Algebra.TensorProduct.basis R b i * Algebra.TensorProduct.basis R b j)) := by
  simp [gramL, Algebra.TensorProduct.basis_apply]

private theorem gramL_mul (s z : R ⊗[k] A) : gramL b s * mat b z = gramL b (s * z) := by
  ext i j
  rw [Matrix.mul_apply, gramL_apply, mul_assoc, mul_left_comm z,
    ← (Algebra.TensorProduct.basis R b).sum_repr (z * _)]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, gramL_apply, mat,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, mul_comm]

private theorem gramL_tr (s : R ⊗[k] A) : (gramL b s)ᵀ = gramL b s := by
  ext i j
  rw [transpose_apply, gramL_apply, gramL_apply, mul_comm (Algebra.TensorProduct.basis R b i)]

private theorem mat_io (c : R ≃ₐ[k] R) (z : R ⊗[k] A) : mat b (io c A z) = (mat b z).map c := by
  have h1 : ∀ y i, (Algebra.TensorProduct.basis R b).repr (io c A y) i =
      c ((Algebra.TensorProduct.basis R b).repr y i) := fun y i => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [io, Algebra.TensorProduct.basis_repr_tmul]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  ext i j
  rw [map_apply, mat, mat, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← h1,
    map_mul (io c A)]
  simp [io, Algebra.TensorProduct.basis_apply]

private theorem mat_one_tmul (x : A) :
    mat b ((1 : R) ⊗ₜ[k] x) = (Algebra.leftMulMatrix b x).map (algebraMap k R) := by
  ext i j
  simp [mat, Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_repr_tmul]

private theorem gramL_eq (s : R ⊗[k] A) : gramL b s = gram R b 1 * mat b s := by
  rw [gram, gramL_mul, ← Algebra.TensorProduct.one_def, one_mul]

end

theorem gramBasic : GramBasic := by
  intro k R _ _ _ A _ _ n b c _
  have hdet : ∀ s, (gramL b s).det = Algebra.norm R s * (gram R b 1).det := fun s => by
    rw [gramL_eq, det_mul, mul_comm, Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R b)]
    rfl
  refine ⟨fun s z => ⟨?_, gramL_mul b s z, ?_, hdet s⟩, fun x => ⟨?_, ?_⟩, fun g hg => ?_⟩
  · rw [ct, ← mat_io, ← gramL_tr b s, ← transpose_mul, gramL_mul, gramL_tr, mul_comm]
  · rw [ct, ← gramL_tr b (io c A s)]
    congr 1
    ext i j
    simp only [map_apply, gramL, of_apply,
      Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b)]
    rw [AddMonoidHom.map_trace]
    refine (congrArg trace (mat_io b c _).symm).trans ?_
    rw [map_mul]
    simp [io, mat]
  · ext i j
    simp only [gram, map_apply, gramL, of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b), Algebra.trace_eq_matrix_trace b]
    rw [AddMonoidHom.map_trace]
    exact congrArg trace (mat_one_tmul b _)
  · rw [gram, gramL_eq, det_mul, mul_comm, mat_one_tmul, Algebra.norm_eq_matrix_det b, RingHom.map_det]
    rfl
  · have hu : IsUnit (gram R b (1 : A)).det := by
      convert (units_of_sep (Algebra.TensorProduct.basis R b) g.val hg.2).1 using 2
      ext i j
      rw [gram, gramL_apply, ← Algebra.TensorProduct.one_def, one_mul, of_apply]
    refine ⟨hu, fun s t hst => ?_, comm_of_sep _ g.val hg.2⟩
    rw [gramL_eq b s, gramL_eq b t] at hst
    exact Algebra.leftMulMatrix_injective _ (((isUnit_iff_isUnit_det _).2 hu).mul_left_cancel hst)

end UpperTheory.ConvolutionTheory.D
