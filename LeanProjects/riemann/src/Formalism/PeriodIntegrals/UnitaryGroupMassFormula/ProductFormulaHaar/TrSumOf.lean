import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase

noncomputable section

open IsDedekindDomain NumberField TensorProduct

namespace PI.ProdFormulaE.Tr

theorem trace_one_tmul {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] [CommRing A] [Algebra R A] (s : S) :
    Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ s) = algebraMap R A (Algebra.trace R S s) := by
  have h : Algebra.lmul A (A ⊗[R] S) (1 ⊗ₜ s) = (Algebra.lmul R S s).baseChange A := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a t
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, CommRing (K i)] [∀ i, Algebra R (K i)] [∀ i, Module.Free R (K i)]
    [∀ i, Module.Finite R (K i)] (z : ∀ i, K i) :
    Algebra.trace R (∀ i, K i) z = ∑ i, Algebra.trace R (K i) (z i) := by
  classical
  let bs := fun i => Module.Free.chooseBasis R (K i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis bs), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (bs i), Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr, bs]

theorem trSum_of (hI : TrInj) (hS : TrSurj) : TrSum := by
  classical
  intro F _ _ ℓ _ ι _ D hD y
  let e : ℚ_[ℓ] ⊗[ℚ] F ≃ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
    AlgEquiv.ofBijective D.Φ ⟨hI F ℓ ι D hD, hS F ℓ ι D hD⟩
  have h1 : e (1 ⊗ₜ y) = fun i => D.ιF i y := by
    funext i
    simp [e, LocFam.Φ, Algebra.TensorProduct.lift_tmul]
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, h1, trace_pi]

end PI.ProdFormulaE.Tr
