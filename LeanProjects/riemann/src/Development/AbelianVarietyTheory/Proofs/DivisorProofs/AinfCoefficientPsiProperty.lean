import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltIsDomainValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistedDivisibilityStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section

namespace GlobalTheory.LemYR

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def phiT : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

theorem phiT_tmul (a : Ainf p O) (l : Λ) : phiT (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l := rfl

theorem phiT_psi {ψ : RL p O Λ →+* RL p O Λ} (hψ : IsPsi ψ) (r : RL p O Λ) : phiT (ψ r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hψ, phiT_tmul, PsiPhi.frobenius_phiInv']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiT_inA (a : Ainf p O) : phiT (inA a : RL p O Λ) = inA (WittVector.frobenius a) := by
  show phiT (a ⊗ₜ 1) = WittVector.frobenius a ⊗ₜ 1
  rfl

theorem repr_phiT {ι : Type} (b : Module.Basis ι ℤ_[p] Λ) (r : RL p O Λ) (i : ι) :
    (Algebra.TensorProduct.basis (Ainf p O) b).repr (phiT r) i =
      WittVector.frobenius ((Algebra.TensorProduct.basis (Ainf p O) b).repr r i) := by
  have hc : ∀ c : ℤ_[p], WittVector.frobenius (algebraMap ℤ_[p] (Ainf p O) c) =
      algebraMap ℤ_[p] (Ainf p O) c := PsiPhi.frobenius_ofPadic
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [phiT_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, hc]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end GlobalTheory.LemYR

open GlobalTheory.LemYR in

theorem GlobalTheory.LemYR.lemY_tensor : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ m : Ainf p O, m.coeff 0 ≠ 0 → ∀ z w : RL p O Λ, z * ψ (inA m) = inA m * w * ψ z → (inA m : RL p O Λ) ∣ z := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ ψ hψ m hm z w hzw
  obtain ⟨hD, hV⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv
  haveI : Module.IsTorsionFree ℤ_[p] Λ := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  set b := Module.finBasis ℤ_[p] Λ
  set B := Algebra.TensorProduct.basis (Ainf p O) b
  have h1 : phiT z * inA m = inA (WittVector.frobenius m) * phiT w * z := by
    have := congrArg phiT hzw
    simpa only [map_mul, phiT_psi hψ, phiT_inA] using this
  have hA : ∀ (a : Ainf p O) (r : RL p O Λ) i, B.repr (inA a * r) i = a * B.repr r i := by
    intro a r i
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have key : ∀ i, m * WittVector.frobenius (B.repr z i) =
      WittVector.frobenius m * (Algebra.leftMulMatrix B (phiT w) *ᵥ fun j => B.repr z j) i := by
    intro i
    have := congrArg (fun r => B.repr r i) h1
    rw [mul_comm, hA, repr_phiT, mul_assoc, hA] at this
    rw [this]
    congr 1
    exact congrFun (Algebra.leftMulMatrix_mulVec_repr B (phiT w) z) i |>.symm
  have hdiv := GlobalTheory.T.frobenius_twisted_divisibility p (PreTilt O p) (Module.finrank ℤ_[p] Λ) m
    (Algebra.leftMulMatrix B (phiT w)) (fun j => B.repr z j) hm key
  choose c hc using hdiv
  refine ⟨∑ i, c i • B i, ?_⟩
  conv_lhs => rw [← B.sum_repr z]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, Algebra.smul_def (m : Ainf p O) (c i • B i)]
