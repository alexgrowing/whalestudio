import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantNonzero

open scoped TensorProduct
open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

private theorem orderOf_gen (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) : orderOf σ = m + 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hm]

private theorem pow_inj (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) :
    Function.Injective (fun i : Fin (m + 1) => σ ^ (i : ℕ)) := by
  have ho := orderOf_gen σ hσ hm
  intro i j hij
  have := pow_injOn_Iio_orderOf (x := σ) (by simp only [ho, Set.mem_Iio]; exact i.2)
    (by simp only [ho, Set.mem_Iio]; exact j.2) hij
  exact Fin.ext this

private theorem det_ne (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (b : Module.Basis (Fin (m + 1)) F E) :
    (Matrix.of fun (i j : Fin (m + 1)) => (σ ^ (i : ℕ)) (b j)).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DeterminantNonzero.det_ne σ hσ hm b

variable {A : Type} [CommRing A] [Algebra F A]

private noncomputable def phi (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) : E ⊗[F] A →ₐ[F] (Fin (m + 1) → A) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom F _ fun i : Fin (m + 1) => p.comp ((σ ^ (i : ℕ) : E ≃ₐ[F] E) : E →ₐ[F] E))
    (Pi.algHom F _ fun _ => AlgHom.id F A)

private theorem phi_tmul (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) (x : E) (a : A) (i : Fin (m + 1)) :
    phi σ p m (x ⊗ₜ a) i = p ((σ ^ (i : ℕ)) x) * a := by
  simp [phi]

private theorem phi_bij (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) : Function.Bijective (phi σ p m) := by
  let b : Module.Basis (Fin (m + 1)) F E := Module.finBasisOfFinrankEq F E hm
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) E := Matrix.of fun i j => (σ ^ (i : ℕ)) (b j)
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne σ hσ hm b)
  let N := M⁻¹
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv _ hunit
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul _ hunit
  let Ψ : (Fin (m + 1) → A) → E ⊗[F] A := fun f => ∑ j, b j ⊗ₜ[F] (∑ i, p (N j i) * f i)
  have hr : Function.RightInverse Ψ (phi σ p m) := by
    intro f
    funext k
    simp only [Ψ, map_sum, Finset.sum_apply, phi_tmul]
    have h1 : ∀ i, ∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i) = if k = i then 1 else 0 := fun i => by
      have h2 := congrArg p (congrFun (congrFun hMN k) i)
      simp only [Matrix.mul_apply, Matrix.one_apply, M, Matrix.of_apply, map_sum, map_mul] at h2
      rw [h2]
      split_ifs <;> simp
    calc _ = ∑ i, (∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i)) * f i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = f k := by
          simp only [h1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hadd : ∀ f g, Ψ (f + g) = Ψ f + Ψ g := fun f g => by
    simp only [Ψ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.tmul_add]
  have hl : Function.LeftInverse Ψ (phi σ p m) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [Ψ]
    | add s t hs ht => rw [map_add, hadd, hs, ht]
    | tmul x a =>
      let c : Fin (m + 1) → E := fun l => algebraMap F E (b.repr x l)
      have hx : (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = M.mulVec c := by
        funext i
        conv_lhs => rw [← b.sum_repr x]
        rw [map_sum]
        simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, c]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Algebra.smul_def, mul_comm]
      have hc : ∀ j, ∑ i, N j i * (σ ^ (i : ℕ)) x = c j := fun j => by
        have : N.mulVec (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = c := by
          rw [hx, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
        exact congrFun this j
      have h3 : ∀ j, ∑ i, p (N j i) * (p ((σ ^ (i : ℕ)) x) * a) = b.repr x j • a := fun j => by
        calc _ = p (∑ i, N j i * (σ ^ (i : ℕ)) x) * a := by
              simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
          _ = _ := by rw [hc]; simp only [c, p.commutes, Algebra.smul_def]
      simp only [Ψ, phi_tmul, h3, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, b.sum_repr]
  exact ⟨hl.injective, hr.surjective⟩

private theorem phi_shift (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) (t : E ⊗[F] A) (i : Fin (m + 1)) :
    phi σ p m (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) t) i = phi σ p m t (i + 1) := by
  have h1 : σ ^ (m + 1) = 1 := by rw [← orderOf_gen σ hσ hm]; exact pow_orderOf_eq_one σ
  have hv : ((i + 1 : Fin (m + 1)) : ℕ) = ((i : ℕ) + 1) % (m + 1) := by simp [Fin.val_add]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, Pi.add_apply, hs, ht]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, phi_tmul, phi_tmul, hv, ← pow_eq_pow_mod _ h1, pow_succ]
    rfl

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.galSplit :
    UpperTheory.ConvolutionTheory.L1.GalSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm A B _ _ _ _ e₀ p
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨e₀.symm.toRingEquiv.trans (RingEquiv.ofBijective (phi σ p m) (phi_bij σ hσ hm p)),
    fun x a i => ?_, fun b i => ?_⟩
  · show phi σ p m (e₀.symm (e₀ (x ⊗ₜ a))) i = _
    rw [AlgEquiv.symm_apply_apply, phi_tmul]
  · show phi σ p m (e₀.symm (galOf e₀ σ b)) i = phi σ p m (e₀.symm b) (i + 1)
    rw [← phi_shift σ hσ hm p]
    have h : e₀.symm (galOf e₀ σ b) =
        Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e₀.symm b) :=
      e₀.symm_apply_apply _
    rw [h]
