import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitDetOfProductMapNeZero

namespace GlobalTheory.TraceDiagonal

open IsLocalRing
open scoped TensorProduct

theorem exists_trace_eq_of_isUnit_det {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {d : ℕ} (b : Module.Basis (Fin d) A R) (M : Matrix (Fin d) (Fin d) A)
    (h : ∀ x : R, (∑ i, ∑ j, M i j • TensorProduct.tmul A (b i) (b j)) *
      (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) = 0) (hu : IsUnit M.det) :
    ∃ lam : R →ₗ[A] A, ∀ x : R,
      Algebra.trace A R x = lam (x * ∑ i, ∑ j, M i j • (b i * b j)) := by
  have hΦ : ∀ f : R →ₗ[A] A, ∑ i, ∑ j, (M i j * f (b i)) • b j
      = b.equivFun.symm (Matrix.vecMul (fun i => f (b i)) M) := by
    intro f
    rw [b.equivFun_symm_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.vecMul, dotProduct, Finset.sum_smul, mul_comm]
  set J : R := ∑ i, ∑ j, M i j • (b i * b j) with hJ
  let lam : R →ₗ[A] A := b.constr A (Matrix.vecMul (b.equivFun 1) M⁻¹)
  have h1 : ∑ i, ∑ j, (M i j * lam (b i)) • b j = 1 := by
    have e : (fun i => lam (b i)) = Matrix.vecMul (b.equivFun 1) M⁻¹ :=
      funext fun i => b.constr_basis A _ i
    rw [hΦ, e, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one,
      LinearEquiv.symm_apply_apply]
  have h2 : ∑ i, ∑ j, (M i j * (lam ∘ₗ LinearMap.mulRight A J) (b i)) • b j = J := by
    have := annihilator_diagonal_form_swap b M h lam J
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
    rw [this]
    simp only [← smul_mul_assoc, ← Finset.sum_mul]
    rw [h1, one_mul]
  have h3 := annihilator_diagonal_trace b M h
  rw [← hJ, ← h2, hΦ, hΦ] at h3
  have h4 := congrArg (fun v => Matrix.vecMul v M⁻¹) (b.equivFun.symm.injective h3)
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] at h4
  have h5 : Algebra.trace A R = lam ∘ₗ LinearMap.mulRight A J := b.ext fun i => congrFun h4 i
  exact ⟨lam, fun x => by rw [h5]; rfl⟩

end GlobalTheory.TraceDiagonal

namespace GlobalTheory

open IsLocalRing

theorem exists_trace_eq_form_mul_diagonal : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (Δ : TensorProduct A R R) (ε : R →+* ResidueField A), ε.comp (algebraMap A R) = residue A → (∀ x : R, ε x = 0 → ∃ m : ℕ, x ^ m ∈ (maximalIdeal A).map (algebraMap A R)) → (∀ x : R, (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) * Δ = 0) → (∀ (s : Finset (R × R)), Δ = ∑ p ∈ s, TensorProduct.tmul A p.1 p.2 → ∀ lift : ResidueField A → A, (∀ z, residue A (lift z) = z) → ∑ p ∈ s, lift (ε p.1) • p.2 ∉ (maximalIdeal A).map (algebraMap A R)) → ∃ lam : R →ₗ[A] A, ∀ x : R, Algebra.trace A R x = lam (x * Algebra.TensorProduct.lmul' (S := R) A Δ) := by
  intro A R _ _ _ _ _ _ Δ ε hε hnil hΔ hne
  classical
  let b := Module.finBasis A R
  let M : Matrix (Fin (Module.finrank A R)) (Fin (Module.finrank A R)) A :=
    Matrix.of fun i j => (b.tensorProduct b).repr Δ (i, j)
  have hM : Δ = ∑ i, ∑ j, M i j • TensorProduct.tmul A (b i) (b j) := by
    conv_lhs => rw [← (b.tensorProduct b).sum_repr Δ, Fintype.sum_prod_type]
    simp [M]
  have hJ : Algebra.TensorProduct.lmul' (S := R) A Δ = ∑ i, ∑ j, M i j • (b i * b j) := by
    rw [hM]; simp
  rw [hJ]
  refine TraceDiagonal.exists_trace_eq_of_isUnit_det b M (fun x => by rw [← hM, mul_comm, hΔ]) ?_
  let k := ResidueField A
  let I : Ideal R := (maximalIdeal A).map (algebraMap A R)
  letI : Algebra k (R ⧸ I) := Ideal.Quotient.algebraQuotientMapQuotient
  haveI : IsScalarTower A k (R ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨lift, hlift⟩ := (residue_surjective (R := A)).hasRightInverse
  have hεa : ∀ a, ε (algebraMap A R a) = residue A a := fun a => RingHom.congr_fun hε a
  let ev : R →ₐ[A] k := { ε with commutes' := hεa }
  have hev : ∀ x, ev x = ε x := fun _ => rfl
  let n : Ideal R := Ideal.span (Set.range fun i => b i - algebraMap A R (lift (ε (b i))))
  obtain ⟨N, hN⟩ : ∃ N, n ^ N ≤ I := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact hnil _ (by rw [map_sub, hεa, hlift, sub_self])
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset Δ
  rw [← Matrix.det_transpose]
  refine DiscrJacobian.isUnit_det_of_productMap_ne_zero (C := R ⧸ I) b n N hN ev ?_ ?_
    (Ideal.Quotient.mkₐ A I) (Algebra.TensorProduct.comm A R R Δ) M.transpose ?_ ?_ ?_
  · intro w hw
    have : n ≤ RingHom.ker ev := Ideal.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, hev]
      rw [map_sub, hεa, hlift, sub_self])
    exact this hw
  · intro w
    refine ⟨∑ i, b.repr w i * lift (ε (b i)), ?_⟩
    have e : w - algebraMap A R (∑ i, b.repr w i * lift (ε (b i)))
        = ∑ i, algebraMap A R (b.repr w i) * (b i - algebraMap A R (lift (ε (b i)))) := by
      conv_lhs => lhs; rw [← b.sum_repr w]
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib, Algebra.smul_def]
    rw [e]
    exact n.sum_mem fun j _ => n.mul_mem_left _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [hM, Finset.sum_comm]
    simp
  · intro x
    have := congrArg (Algebra.TensorProduct.comm A R R) (hΔ x)
    rw [map_mul, map_sub, map_zero, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.comm_tmul] at this
    linear_combination -this
  · intro h0
    refine hne s hs lift hlift (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    rw [← h0, hs, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : algebraMap k (R ⧸ I) (ε p.1) = Ideal.Quotient.mk I (algebraMap A R (lift (ε p.1))) := by
      conv_lhs => rw [← hlift (ε p.1)]
      rfl
    rw [Algebra.smul_def, map_mul, ← e, mul_comm]
    rfl

end GlobalTheory
