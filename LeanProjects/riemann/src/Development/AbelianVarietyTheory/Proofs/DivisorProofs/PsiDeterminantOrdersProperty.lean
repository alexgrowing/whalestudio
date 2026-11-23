import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeLatticeElementPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfCoefficientPsiPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfLeadOrdersEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfTwistedEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_detElt_orders_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N : ℕ) (Δ Δ' : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ → IsDetElt ε ψ N Δ' → HasOrders C ε N Δ a c → HasOrders C ε N Δ' a c' → Δ ∣ Δ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N Δ Δ' a c c' hD hD' hO hO'
  obtain ⟨hAdom, -, hker, -, hnu, hxi, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨hmu0, hmu, -⟩ := GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hinA : ∀ x : Ainf p O, (inA x : RL p O Λ) = x ⊗ₜ[ℤ_[p]] (1 : Λ) := fun x => by
    first | rfl | simp [inA, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self]
  have hθ : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∀ x, f (inA x) = WittVector.fontaineTheta O p x := by
    intro σ f hf x; rw [hinA, hf, map_one, mul_one]
  have hθxi : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  have hψmu : ψ (inA (mu ε)) = inA (nu ε) := by
    rw [hinA, hψ, hinA, phiInv_mu]

  have hu' : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → algebraMap O C (f (ψ Δ')) ≠ 0 := by
    intro σ f hf h0
    obtain ⟨k, hk⟩ := hD'.1
    have h1 := congrArg (fun x => algebraMap O C (f (ψ x))) hk
    simp only [map_pow, map_mul, hψmu, hθ σ f hf, h0, zero_mul] at h1
    exact pow_ne_zero N ((map_ne_zero_iff _ hinj).mpr hnu) h1
  obtain ⟨g, hΔg, g₁, hgg⟩ := hD.2
  obtain ⟨g', hΔg', -⟩ := hD'.2
  let ι := {q : (Λ →+* O) × (RL p O Λ →+* O) // IsTheta q.1 q.2}
  have hξ : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.DetInv.inA_mem_nonZeroDivisors p C v O hv ε hε Λ (xi ε) hxi
  obtain ⟨b, hb⟩ := GlobalTheory.DetInv.dvd_of_lead_orders_eq (RL p O Λ) C ι
    (fun i => (algebraMap O C).comp i.1.2) (inA (xi ε)) N (fun i => a i.1.1)
    (fun i => c i.1.1) (fun i => c' i.1.1) Δ Δ' (ψ Δ) (ψ Δ') g g' g₁ hξ
    (fun i => by
      show algebraMap O C (i.1.2 (inA (xi ε))) = 0
      rw [hθ _ _ i.2, hθxi, map_zero])
    (fun r hr => GlobalTheory.T.relative_lattice_element_property p C v O hv ε hε Λ r (fun σ f hf => hinj (by
      simpa using hr ⟨(σ, f), hf⟩)))
    (fun i => (hO i.1.1 i.1.2 i.2).1) (fun i => (hO i.1.1 i.1.2 i.2).2.1)
    (fun i => (hO i.1.1 i.1.2 i.2).2.2) (fun i => (hO' i.1.1 i.1.2 i.2).2.2)
    hΔg hΔg' (fun i => by simpa using hu' i.1.1 i.1.2 i.2) hgg.symm
  haveI := hAdom
  obtain ⟨Δs, hΔs⟩ := hD.1
  have hcoeff : (mu ε ^ N).coeff 0 ≠ 0 := by
    haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
    have : ∀ n : ℕ, (mu ε ^ n).coeff 0 = (mu ε).coeff 0 ^ n := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, WittVector.mul_coeff_zero, ih, pow_succ]
    rw [this]; exact pow_ne_zero N hmu0
  refine GlobalTheory.DetInv.dvd_of_twisted_eq (RL p O Λ) ψ (inA (mu ε ^ N)) Δ Δs Δ' g b
    (GlobalTheory.DetInv.inA_mem_nonZeroDivisors p C v O hv ε hε Λ _ (pow_ne_zero N hmu))
    (by
      show Δ * Δs = algebraMap (Ainf p O) (RL p O Λ) (mu ε ^ N)
      rw [map_pow]; exact hΔs.symm) hΔg (by rw [hb] at hΔg'; exact hΔg') ?_
  exact GlobalTheory.T.ainf_coefficient_psi_property p C v O hv Λ ψ hψ (mu ε ^ N) hcoeff

end GlobalTheory.DetInv
