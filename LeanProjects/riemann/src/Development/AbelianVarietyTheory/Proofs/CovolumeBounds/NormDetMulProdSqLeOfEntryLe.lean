import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete

open scoped TensorProduct Matrix
open Module Algebra

namespace GlobalTheory

section Pi

variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]

theorem leftMulMatrix_pi_basisFun [DecidableEq ι] (x : ι → E) :
    leftMulMatrix (Pi.basisFun E ι) x = Matrix.diagonal x := by
  ext i j
  rw [leftMulMatrix_eq_repr_mul]
  by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]

theorem algebraTrace_pi_apply (x : ι → E) : Algebra.trace E (ι → E) x = ∑ i, x i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E ι), leftMulMatrix_pi_basisFun,
    Matrix.trace_diagonal]

end Pi

section BaseChange

variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing E]
  [Algebra R E] [Module.Free R S] [Module.Finite R S]

theorem algebraTrace_one_tmul (x : S) :
    Algebra.trace E (E ⊗[R] S) (1 ⊗ₜ x) = algebraMap R E (Algebra.trace R S x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

end BaseChange

section Split

variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]

variable (R S) in

theorem exists_algEquiv_fin_points :
    ∃ (n : ℕ) (P : Fin n ≃ (S →ₐ[R] E)) (e : E ⊗[R] S ≃ₐ[E] (Fin n → E)),
      ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun E (E ⊗[R] S)
  let f : Fin n → (E ⊗[R] S →ₐ[E] E) := fun j ↦
    (Pi.evalAlgHom E (fun _ ↦ E) j).comp e.toAlgHom
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      by_contra h
      have := AlgHom.congr_fun hij (e.symm (Pi.single i 1))
      simp [f, Ne.symm h] at this
    · intro g
      obtain ⟨j, hj⟩ := AlgHom.eq_piEvalAlgHom (g.comp e.symm.toAlgHom)
      refine ⟨j, AlgHom.ext fun x ↦ ?_⟩
      simpa [f] using (AlgHom.congr_fun hj (e x)).symm
  exact ⟨n, (Equiv.ofBijective f hf).trans (AlgHom.liftEquiv R E S E).symm, e, fun x j ↦ rfl⟩

variable (R S) in
theorem finite_algHom_of_isFiniteSplit : Finite (S →ₐ[R] E) := by
  obtain ⟨n, P, -⟩ := exists_algEquiv_fin_points R S E
  exact Finite.of_equiv _ P

variable {E} in

theorem exists_algEquiv_points {ι : Type*} (P : ι ≃ (S →ₐ[R] E)) :
    ∃ e : E ⊗[R] S ≃ₐ[E] (ι → E), ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  obtain ⟨n, Q, e, he⟩ := exists_algEquiv_fin_points R S E
  refine ⟨e.trans (AlgEquiv.piCongrLeft' E (fun _ ↦ E) (Q.trans P.symm)), fun x j ↦ ?_⟩
  simp [he]

variable [Module.Free R S]

variable (R S) in

theorem natCard_algHom_eq_finrank [Nontrivial R] : Nat.card (S →ₐ[R] E) = finrank R S := by
  obtain ⟨n, P, e, -⟩ := exists_algEquiv_fin_points R S E
  rw [← Nat.card_congr P, ← Module.finrank_baseChange (R := E), e.toLinearEquiv.finrank_eq]
  simp

variable {E} {ι : Type*} [Fintype ι]

theorem card_eq_finrank_of_points (P : ι ≃ (S →ₐ[R] E)) : Fintype.card ι = finrank R S := by
  have := (algebraMap R E).domain_nontrivial
  rw [← natCard_algHom_eq_finrank R S E, ← Nat.card_congr P, Nat.card_eq_fintype_card]

variable [Module.Finite R S]

theorem algebraMap_trace_eq_sum_points (P : ι ≃ (S →ₐ[R] E)) (x : S) :
    algebraMap R E (Algebra.trace R S x) = ∑ j, P j x := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  rw [← algebraTrace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, algebraTrace_pi_apply]
  simp [he]

variable [DecidableEq ι]

theorem det_points_sq_eq_discr (P : ι ≃ (S →ₐ[R] E)) (v : ι → S) :
    (Matrix.of fun i j ↦ P j (v i)).det ^ 2 = algebraMap R E (discr R v) := by
  have : (algebraMap R E).mapMatrix (traceMatrix R v) =
      (Matrix.of fun i j ↦ P j (v i)) * (Matrix.of fun i j ↦ P j (v i))ᵀ := by
    ext i j
    simp [Matrix.mul_apply, algebraMap_trace_eq_sum_points P]
  rw [discr_def, RingHom.map_det, this, Matrix.det_mul, Matrix.det_transpose, pow_two]

omit [Module.Free R S] [Module.Finite R S] in

theorem det_points_ne_zero_of_basis (P : ι ≃ (S →ₐ[R] E)) (b : Basis ι R S) :
    (Matrix.of fun i j ↦ P j (b i)).det ≠ 0 := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  have h := (Pi.basisFun E ι).isUnit_det ((Algebra.TensorProduct.basis E b).map e.toLinearEquiv)
  rw [Basis.det_apply, ← Matrix.det_transpose] at h
  convert h.ne_zero using 2
  ext i j
  simp [Basis.toMatrix_apply, Algebra.TensorProduct.basis_apply, he]

end Split

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

end General

section Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Hadamard

section Etale

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]

variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_points_ne_zero_iff {E : Type*} [Field E] [Algebra K E] [Module.Finite K A]
    [IsFiniteSplit E (E ⊗[K] A)] (P : ι ≃ (A →ₐ[K] E)) (v : ι → A) :
    (Matrix.of fun i j ↦ P j (v i)).det ≠ 0 ↔ LinearIndependent K v := by
  constructor
  · intro h
    by_contra hli
    have := det_points_sq_eq_discr P v
    rw [discr_zero_of_not_linearIndependent K hli, map_zero] at this
    exact pow_ne_zero 2 h this
  · intro h
    simpa using det_points_ne_zero_of_basis P
      (basisOfLinearIndependentOfCardEqFinrank' v h (card_eq_finrank_of_points P))

theorem discr_ne_zero_iff_of_etale [Algebra.Etale K A] (h : Fintype.card ι = finrank K A)
    (v : ι → A) : discr K v ≠ 0 ↔ LinearIndependent K v := by
  have := FormallyUnramified.finite_of_free K A
  have := finite_algHom_of_isFiniteSplit K A (AlgebraicClosure K)
  obtain ⟨P⟩ : Nonempty (ι ≃ (A →ₐ[K] AlgebraicClosure K)) := by
    rw [← Finite.card_eq, natCard_algHom_eq_finrank, Nat.card_eq_fintype_card, h]
  rw [← det_points_ne_zero_iff P, ← pow_ne_zero_iff (a := Matrix.det _) two_ne_zero,
    det_points_sq_eq_discr]
  simp

end Etale

section DiscrBaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]

end DiscrBaseChange

end GlobalTheory
