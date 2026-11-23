import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Descent

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem desc_alg {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hG : IsGal c 2)
    (L : Type) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L] (s : L →ₐ[k] L)
    (hs : ∀ r, s (algebraMap R L r) = algebraMap R L (c r)) (hss : ∀ z, s (s z) = z) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (e : R ⊗[k] A ≃ₐ[R] L), ∀ z, e (io c A z) = s (e z) := by
  let A : Subalgebra k L := AlgHom.equalizer s (AlgHom.id k L)
  let f : R ⊗[k] A →ₐ[R] L := Algebra.TensorProduct.lift (Algebra.ofId R L) A.val fun _ _ => Commute.all _ _
  have hf : ∀ (r : R) (a : A), f (r ⊗ₜ a) = algebraMap R L r * a := fun r a => rfl
  have hb := descent k R c 2 hG L s.toLinearMap
    (fun r m => by simp [Algebra.smul_def, hs]) (LinearMap.ext fun z => by simp [pow_two, hss])
  let j : A ≃ₗ[k] LinearMap.eqLocus s.toLinearMap LinearMap.id :=
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbij : Function.Bijective f := by
    have h2 := hb.comp (j.lTensor R).bijective
    convert h2 using 1
    funext z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [Function.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]
    | tmul r a => rw [hf, ← Algebra.smul_def]; rfl
  refine ⟨A, inferInstance, inferInstance, AlgEquiv.ofBijective f hbij, fun z => ?_⟩
  change f _ = s (f z)
  induction z with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r a =>
    have h1 : io c A (r ⊗ₜ a) = c r ⊗ₜ a := by simp [io]
    have h2 : s a = a := a.2
    rw [h1, hf, hf, map_mul, hs, h2]

private theorem inv_ex {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1)
    {n : ℕ} {P : R[X]} (hP : IsCsr c n P) :
    ∃ s : AdjoinRoot P →ₐ[k] AdjoinRoot P, (∀ r, s (algebraMap R _ r) = algebraMap R _ (c r)) ∧ (∀ z, s (s z) = z) ∧
      AdjoinRoot.root P * s (AdjoinRoot.root P) = 1 := by
  obtain ⟨hm, hn, hu, hr⟩ := hP
  have hcc : ∀ r, c (c r) = r := fun r => by
    rw [← AlgEquiv.mul_apply, ← pow_two, hc]; rfl
  have hx : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * P.divX + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add, AdjoinRoot.mk_self]
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 := (hu.map (AdjoinRoot.of P)).neg
    rw [← eq_neg_of_add_eq_zero_left h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  letI : Invertible y := ⟨AdjoinRoot.root P, hy, by rw [mul_comm, hy]⟩
  have h0 : P.eval₂ ((AdjoinRoot.of P).comp (c : R →+* R)) y = 0 := by
    rw [← eval₂_map, ← eval₂_reflect_eq_zero_iff _ y n _ (natDegree_map_le.trans hn.le), hr, eval₂_mul]
    exact mul_eq_zero_of_right _ (AdjoinRoot.eval₂_root P)
  let s0 : AdjoinRoot P →+* AdjoinRoot P := AdjoinRoot.lift _ y h0
  have h1 : ∀ r, s0 (AdjoinRoot.of P r) = AdjoinRoot.of P (c r) := fun r => AdjoinRoot.lift_of h0
  have h2 : s0 (AdjoinRoot.root P) = y := AdjoinRoot.lift_root h0
  have h3 : s0 y = AdjoinRoot.root P := by
    have := congrArg s0 hy
    rw [map_mul, map_one, h2] at this
    calc s0 y = (AdjoinRoot.root P * y) * s0 y := by rw [hy, one_mul]
      _ = _ := by rw [mul_assoc, this, mul_one]
  refine ⟨⟨s0, fun a => ?_⟩, h1, fun z => ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply k R (AdjoinRoot P)]
    exact (h1 _).trans (by rw [c.commutes]; rfl)
  · change s0 (s0 z) = z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    induction p using Polynomial.induction_on with
    | C a => rw [AdjoinRoot.mk_C, h1, h1, hcc]
    | add a b ha hb => simp only [map_add, ha, hb]
    | monomial m a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, ih, AdjoinRoot.mk_X, h2, h3]
  · change _ * s0 _ = 1
    rw [h2, hy]

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.modelEx :
    UpperTheory.ConvolutionTheory.D.ModelEx := by
  intro k R _ _ _ _ c hG n P hP hsep
  obtain ⟨s, hs, hss, hx⟩ := inv_ex c hG.pow hP
  obtain ⟨A, _, _, e, he⟩ := desc_alg c hG (AdjoinRoot P) s hs hss
  obtain ⟨-, -, hff, -⟩ := galBase k R k c 2 hG
  obtain ⟨hm, hn, -, -⟩ := hP
  haveI : Nontrivial R := hG.inj.nontrivial
  let B := (AdjoinRoot.powerBasis' hm).basis.map e.symm.toLinearEquiv
  haveI : Module.Finite R (R ⊗[k] A) := Module.Finite.of_basis B
  haveI : Module.Free R (R ⊗[k] A) := Module.Free.of_basis B
  haveI : Module.Finite k A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R
  haveI : Module.Flat k A := Module.Flat.of_flat_tensorProduct k A R
  haveI : Module.Free k A := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank k A = n := by
    rw [← Module.finrank_baseChange (R := R), Module.finrank_eq_card_basis B, Fintype.card_fin, ← hn]
    rfl
  let b := Module.finBasisOfFinrankEq k A hr
  have h1 : e.symm (AdjoinRoot.root P) * io c A (e.symm (AdjoinRoot.root P)) = 1 := by
    apply e.injective
    rw [map_mul, he, e.apply_symm_apply, hx, map_one]
  let g : (R ⊗[k] A)ˣ := Units.mkOfMulEqOne _ _ h1
  have h2 : cp (matU b g) = P := by
    set M := Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b) (e.symm (AdjoinRoot.root P)) with hM
    change M.charpoly = P
    have h3 : aeval (AdjoinRoot.root P) M.charpoly = 0 := by
      have h4 := Matrix.aeval_self_charpoly M
      rw [hM, aeval_algHom_apply, ← hM, map_eq_zero_iff _ (Algebra.leftMulMatrix_injective _),
        aeval_algHom_apply] at h4
      exact (map_eq_zero_iff _ e.symm.injective).1 h4
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h3
    exact eq_of_monic_of_dvd_of_natDegree_le hm M.charpoly_monic h3
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hn])
  exact ⟨A, _, _, b, g, ⟨h1, h2 ▸ hsep⟩, h2⟩
