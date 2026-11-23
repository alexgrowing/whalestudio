import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.RepNmSucc
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {σ : R ≃ₐ[k] R} {q n : ℕ}

private theorem isUnit_of_map (h : IsGal σ q) {x : k} (hx : IsUnit (algebraMap k R x)) : IsUnit x := by
  obtain ⟨r, hr⟩ := hx.exists_right_inv
  have h1 : algebraMap k R x * σ r = 1 := by
    rw [← σ.commutes, ← map_mul, hr, map_one]
  obtain ⟨y, hy⟩ := h.fix r (hx.mul_left_cancel (h1.trans hr.symm))
  refine IsUnit.of_mul_eq_one y (h.inj ?_)
  rw [map_mul, hy, hr, map_one]

private theorem separable_of_map (h : IsGal σ q) {p : k[X]} (hp : p.Monic)
    (hs : (p.map (algebraMap k R)).Separable) [Nontrivial k] : p.Separable := by
  haveI : Nontrivial R := h.inj.nontrivial
  rw [Polynomial.separable_def] at hs ⊢
  rw [← Polynomial.isUnit_resultant_iff_isCoprime (hp.map _), Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective h.inj, Polynomial.natDegree_map_eq_of_injective h.inj,
    Polynomial.resultant_map_map] at hs
  rw [← Polynomial.isUnit_resultant_iff_isCoprime hp]
  exact isUnit_of_map h hs

private theorem exists_model [Nontrivial k] {p : k[X]} (hp : p.Monic) (hn : p.natDegree = n) :
    ∃ (b : Module.Basis (Fin n) k (AdjoinRoot p)),
      (Algebra.leftMulMatrix b (AdjoinRoot.root p)).charpoly = p := by
  subst hn
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin p.natDegree) k (AdjoinRoot p)) :=
    ⟨(AdjoinRoot.powerBasis' hp).basis⟩
  refine ⟨b, ?_⟩
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp (Matrix.charpoly_monic _) ?_ ?_
  · rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]
  · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

private theorem sgConj_mul (x y d : GL (Fin n) R) : sgConj σ (x * y) d = sgConj σ y (sgConj σ x d) := by
  simp only [sgConj, map_mul, _root_.mul_inv_rev, mul_assoc]

private theorem sgConj_one (d : GL (Fin n) R) : sgConj σ 1 d = d := by
  simp [sgConj]

variable {A : Type} [CommRing A] [Algebra k A]

private theorem mat_tmul (b : Module.Basis (Fin n) k A) (r : R) (s : A) :
    mat b (r ⊗ₜ[k] s) = r • (Algebra.leftMulMatrix b s).map (algebraMap k R) := by
  ext i j
  simp [mat, Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_repr_tmul]

private def phi (b : Module.Basis (Fin n) k A) : A ⊗[k] R →+* Matrix (Fin n) (Fin n) R :=
  (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b)).toRingHom.comp
    (Algebra.TensorProduct.comm k A R).toRingEquiv.toRingHom

private theorem phi_inj (b : Module.Basis (Fin n) k A) : Function.Injective (phi (R := R) b) :=
  (Algebra.leftMulMatrix_injective (Algebra.TensorProduct.basis R b)).comp
    (Algebra.TensorProduct.comm k A R).injective

private theorem phi_tmul (b : Module.Basis (Fin n) k A) (r : R) (s : A) :
    phi b (s ⊗ₜ[k] r) = r • (Algebra.leftMulMatrix b s).map (algebraMap k R) :=
  mat_tmul b r s

private theorem phi_aeval (b : Module.Basis (Fin n) k A) (s : A) (P : R[X]) :
    ∃ t, phi b t = aeval ((Algebra.leftMulMatrix b s).map (algebraMap k R)) P := by
  refine ⟨(Algebra.TensorProduct.comm k A R).symm (aeval ((1 : R) ⊗ₜ[k] s) P), ?_⟩
  have h1 := mat_tmul b (1 : R) s
  rw [one_smul, mat] at h1
  rw [← h1, Polynomial.aeval_algHom_apply]
  simp [phi]

private theorem phi_sg (b : Module.Basis (Fin n) k A) (t : A ⊗[k] R) :
    phi b ((Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) t) =
      (phi b t).map σ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s r =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, phi_tmul, phi_tmul]
    ext i j
    simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.map_add _ (map_add σ)]

private theorem phi_pow (b : Module.Basis (Fin n) k A) (j : ℕ) (t : A ⊗[k] R) :
    phi b (((Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) ^ j) t) =
      (phi b t).map (σ ^ j) := by
  induction j with
  | zero => ext; simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, phi_sg, ih]
    ext
    simp [pow_succ']

private theorem phi_nm (b : Module.Basis (Fin n) k A) (t : A ⊗[k] R) (a : GL (Fin n) R)
    (ha : phi b t = a) (m : ℕ) :
    phi b (∏ j ∈ Finset.range m,
      ((Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) ^ j) t) =
      nm σ m a := by
  induction m with
  | zero => simp [nm]
  | succ m ih =>
    rw [Finset.prod_range_succ, map_mul, ih, phi_pow, ha, nm, nm, List.prod_range_succ,
      Units.val_mul]
    rfl

end

theorem nmInj : NmInj := by
  intro k R _ _ _ _ σ q h n δ δ' hs he
  haveI : Nontrivial R := h.inj.nontrivial
  obtain ⟨⟨p, hp, hpe⟩, -⟩ := nmPoly k R σ q h n δ
  have hn : p.natDegree = n := by
    rw [← Polynomial.natDegree_map_eq_of_injective h.inj, ← hpe, cp,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨b, hb⟩ := exists_model hp hn
  have hu : IsUnit (Algebra.leftMulMatrix b (AdjoinRoot.root p)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine isUnit_of_map h ?_
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 (nm σ q δ).isUnit
    rw [Matrix.det_eq_sign_charpoly_coeff] at h1 ⊢
    rw [cp] at hpe
    rw [hpe, Polynomial.coeff_map] at h1
    simpa [hb] using h1
  obtain ⟨γ, hγ⟩ := hu
  have hcp : cp γ = p := by rw [cp, hγ, hb]
  have hsp : (cp γ).Separable := by
    rw [hcp]; exact separable_of_map h hp (hpe ▸ hs)
  obtain ⟨x, hx, hxc⟩ := nmRep k R σ q h n δ γ hsp (by rw [hcp, hpe])
  obtain ⟨x', hx', hxc'⟩ := nmRep k R σ q h n δ' γ hsp (by rw [hcp, he, hpe])
  obtain ⟨hfin, -, -, hT⟩ := galBase k R (AdjoinRoot p) σ q h
  have hG : ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (Algebra.leftMulMatrix b (AdjoinRoot.root p)).map (algebraMap k R) := by
    rw [← hγ]; rfl
  obtain ⟨-, hcent, -⟩ := conjSep k R n (up R γ : GL (Fin n) R) (by
    rw [hG, Matrix.charpoly_map, hb, ← hpe]; exact hs)
  have key : ∀ a : GL (Fin n) R, Commute a (up R γ) →
      ∃ t : (AdjoinRoot p ⊗[k] R)ˣ, Units.map (phi b).toMonoidHom t = a := by
    have k0 : ∀ a : GL (Fin n) R, Commute a (up R γ) → ∃ t : AdjoinRoot p ⊗[k] R, phi b t = a := by
      intro a ha
      obtain ⟨P, hP⟩ := hcent a (by rw [← Units.val_mul, ha.eq, Units.val_mul])
      rw [hP, hG]
      exact phi_aeval b _ P
    intro a ha
    obtain ⟨t, ht⟩ := k0 a ha
    obtain ⟨t', ht'⟩ := k0 a⁻¹ ha.inv_left
    have h1 : t * t' = 1 := phi_inj b (by
      rw [map_mul, ht, ht', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    exact ⟨Units.mkOfMulEqOne t t' h1, Units.ext ht⟩
  obtain ⟨t, ht⟩ := key _ hxc
  obtain ⟨t', ht'⟩ := key _ hxc'
  haveI : Module.Finite k (AdjoinRoot p) := Module.Finite.of_basis b
  set τ : AdjoinRoot p ⊗[k] R ≃ₐ[AdjoinRoot p] AdjoinRoot p ⊗[k] R :=
    Algebra.TensorProduct.congr AlgEquiv.refl σ with hτ
  have hN : ∏ j ∈ Finset.range q, (τ ^ j) t = ∏ j ∈ Finset.range q, (τ ^ j) t' := by
    apply phi_inj b
    rw [phi_nm b _ _ (congrArg Units.val ht), phi_nm b _ _ (congrArg Units.val ht'), hx, hx']
  obtain ⟨z, hz⟩ := h90 k R (AdjoinRoot p) _ τ q hT (t * t'⁻¹) (by
    simp only [Units.val_mul, map_mul]
    rw [Finset.prod_mul_distrib, hN, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← map_mul, Units.mul_inv, map_one])
  have hz' : (t : AdjoinRoot p ⊗[k] R) * τ z = z * t' := by
    conv_rhs => rw [← hz]
    rw [Units.val_mul, mul_right_comm, Units.inv_mul_cancel_right]
  have hfinal : sgConj σ (Units.map (phi b).toMonoidHom z) (sgConj σ x δ) = sgConj σ x' δ' := by
    rw [← ht, ← ht', sgConj, mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    have h1 := congrArg (phi b) hz'
    rw [map_mul, map_mul, hτ, phi_sg] at h1
    exact h1
  refine ⟨x * Units.map (phi b).toMonoidHom z * x'⁻¹, ?_⟩
  rw [sgConj_mul, sgConj_mul, hfinal, ← sgConj_mul, mul_inv_cancel, sgConj_one]

end UpperTheory.ConvolutionTheory.D
