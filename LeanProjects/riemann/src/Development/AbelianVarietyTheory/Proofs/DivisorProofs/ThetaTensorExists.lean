import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonicalStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem theta_tensor_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p),
    IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (σ : Λ →+* O),
    ∃ f : RL p O Λ →+* O, IsTheta σ f ∧ Function.Surjective f ∧ f (inA (xi ε)) = 0 ∧
      f (inA (nu ε)) ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ σ
  obtain ⟨-, -, hker, hsurj, hnu, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  letI : Algebra ℤ_[p] O := (padicToO p O).toAlgebra
  let θ' : Ainf p O →ₐ[ℤ_[p]] O :=
    { WittVector.fontaineTheta O p with commutes' := fun r => rfl }
  have hσ : σ.comp (algebraMap ℤ_[p] Λ) = padicToO p O := GlobalTheory.T.padic_ring_hom_eq_canonical p O _
  have hσr : ∀ r : ℤ_[p], σ (algebraMap ℤ_[p] Λ r) = algebraMap ℤ_[p] O r := fun r => by
    rw [← RingHom.comp_apply, hσ]; rfl
  let σ' : Λ →ₐ[ℤ_[p]] O := { σ with commutes' := hσr }
  let f := (Algebra.TensorProduct.productMap θ' σ').toRingHom
  have hf : ∀ (a : Ainf p O) (l : Λ), f (a ⊗ₜ l) = WittVector.fontaineTheta O p a * σ l := by
    intro a l
    simp [f, θ', σ', Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  have hA : ∀ a : Ainf p O, f (inA a) = WittVector.fontaineTheta O p a := by
    intro a
    show f (algebraMap (Ainf p O) (RL p O Λ) a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, hf]
    simp
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨inA a, hA a⟩
  · rw [hA]
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    exact this
  · rw [hA]; exact hnu

end GlobalTheory.DetInv
