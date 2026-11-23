import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdOfDvdIterates

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SandwichRigid

section Abstract

variable {A : Type} [CommRing A] [IsDomain A]

theorem cancel_smul {m n : ℕ} {a : A} (ha : a ≠ 0) {X Y : Matrix (Fin m) (Fin n) A}
    (hXY : a • X = a • Y) : X = Y := by
  ext i j
  have := congrFun (congrFun hXY i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ ha this

theorem cancel_right {m n : ℕ} {F : Matrix (Fin n) (Fin n) A} (hF : F.det ≠ 0)
    {X Y : Matrix (Fin m) (Fin n) A} (hXY : X * F = Y * F) : X = Y := by
  apply cancel_smul hF
  have := congrArg (· * F.adjugate) hXY
  simpa only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] using this

theorem det_ne_zero_of_mul {n : ℕ} {a : A} (ha : a ≠ 0) {F G : Matrix (Fin n) (Fin n) A}
    (h : G * F = a • (1 : Matrix (Fin n) (Fin n) A)) : F.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem mul_comm_smul_one {n : ℕ} {a : A} (ha : a ≠ 0) {F G : Matrix (Fin n) (Fin n) A}
    (h : G * F = a • (1 : Matrix (Fin n) (Fin n) A)) :
    F * G = a • (1 : Matrix (Fin n) (Fin n) A) := by
  apply cancel_right (det_ne_zero_of_mul ha h)
  rw [Matrix.mul_assoc, h]
  simp

end Abstract

section Witt

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem G_eq [IsDomain (Ainf p O)] {ε : PreTilt O p} (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0)
    {h : ℕ} {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ] (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply cancel_right (det_ne_zero_of_mul hμ D.G_mul_F)
  have h1 : D.Ψ' * D.Ψ = xi ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    mul_comm_smul_one hξ D.Ψ_mul
  have h2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
  have h3 : D.G.map (phiInv p O) * D.F.map (phiInv p O)
      = nu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    rw [← Matrix.map_mul, D.G_mul_F, ← phiInv_mu]
    ext1 i j
    by_cases hij : i = j <;> simp [hij]
  rw [Matrix.mul_assoc, h2, Matrix.mul_smul, h3, smul_smul, xi_mul_nu, D.G_mul_F]

end Witt

end GlobalTheory.SandwichRigid
