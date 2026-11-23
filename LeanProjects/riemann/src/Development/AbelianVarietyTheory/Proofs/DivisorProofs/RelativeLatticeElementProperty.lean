import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingMatrixIndependent
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_xi_of_theta_tensor_vanish : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ r : RL p O Λ, (∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = 0) → (inA (xi ε) : RL p O Λ) ∣ r := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ r hr
  classical
  obtain ⟨-, -, hker, -, -, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  let b := Module.finBasis ℤ_[p] Λ
  let B := Algebra.TensorProduct.basis (Ainf p O) b
  have hrsum : r = ∑ j, B.repr r j ⊗ₜ b j := by
    conv_lhs => rw [← B.sum_repr r]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hθ : ∀ j, WittVector.fontaineTheta O p (B.repr r j) = 0 := by
    have hc := GlobalTheory.embedding_matrix_independent p C v O hv Λ _ b
      (fun j => algebraMap O C (WittVector.fontaineTheta O p (B.repr r j))) (by
        intro σ
        obtain ⟨f, hf, -⟩ := theta_tensor_exists p C v O hv ε hε Λ σ
        have h0 := hr σ f hf
        rw [hrsum, map_sum] at h0
        simp_rw [show ∀ a l, f (a ⊗ₜ l) = _ from hf] at h0
        have h1 := congrArg (algebraMap O C) h0
        simpa [map_sum, map_mul] using h1)
    intro j
    have := congrFun hc j
    exact hv.hom_inj (by simpa using this)
  rw [hrsum]
  refine Finset.dvd_sum fun j _ => ?_
  have hmem : B.repr r j ∈ Ideal.span {xi ε} := by
    rw [← hker]; exact hθ j
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨c ⊗ₜ b j, ?_⟩
  show _ = (xi ε ⊗ₜ[ℤ_[p]] (1 : Λ)) * _
  rw [← hc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]

end GlobalTheory.DetInv
