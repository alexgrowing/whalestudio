import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.Twist

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def phiR : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

def psiR : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.phiInvAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

theorem phiR_tmul (a : Ainf p O) (l : Λ) : phiR (a ⊗ₜ[ℤ_[p]] l) = WittVector.frobenius a ⊗ₜ l := rfl

theorem psiR_tmul (a : Ainf p O) (l : Λ) : psiR (a ⊗ₜ[ℤ_[p]] l) = phiInv p O a ⊗ₜ l := rfl

theorem eq_psiR {ψ : RL p O Λ →+* RL p O Λ} (hψ : IsPsi ψ) (r : RL p O Λ) : ψ r = psiR r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hψ, psiR_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiR_psiR (r : RL p O Λ) : phiR (psiR r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [psiR_tmul, phiR_tmul, PsiPhi.frobenius_phiInv']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem psiR_phiR (r : RL p O Λ) : psiR (phiR r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [phiR_tmul, psiR_tmul, PsiPhi.phiInv_frobenius']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiR_smul (a : Ainf p O) (r : RL p O Λ) :
    phiR (a • r) = WittVector.frobenius a • phiR r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x l => rw [TensorProduct.smul_tmul', phiR_tmul, phiR_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem phiR_one_tmul_mul (l : Λ) (r : RL p O Λ) :
    phiR (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) * r) = ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) * phiR r := by
  rw [map_mul, phiR_tmul, map_one]

variable {N h : ℕ}

def twist (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) :
    (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O) where
  toFun w := fun j => phiInv p O (e (fun i => phiR (w i)) j)
  invFun v := fun i => psiR (e.symm (fun j => WittVector.frobenius (v j)) i)
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, map_add]
    rw [show (fun i => phiR (x i) + phiR (y i)) = (fun i => phiR (x i)) + fun i => phiR (y i) from rfl,
      map_add, Pi.add_apply, map_add]
  map_smul' a x := by
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply, phiR_smul, smul_eq_mul]
    rw [show (fun i => WittVector.frobenius a • phiR (x i)) =
      WittVector.frobenius a • (fun i => phiR (x i)) from rfl, map_smul, Pi.smul_apply, smul_eq_mul,
      map_mul, PsiPhi.phiInv_frobenius']
  left_inv w := by
    funext i
    simp only [PsiPhi.frobenius_phiInv']
    rw [show (fun j => e (fun i => phiR (w i)) j) = e (fun i => phiR (w i)) from rfl,
      LinearEquiv.symm_apply_apply, psiR_phiR]
  right_inv v := by
    funext j
    simp only [phiR_psiR]
    rw [show (fun i => e.symm (fun j => WittVector.frobenius (v j)) i) =
      e.symm (fun j => WittVector.frobenius (v j)) from rfl, LinearEquiv.apply_symm_apply,
      PsiPhi.phiInv_frobenius']

theorem twist_apply (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (w) :
    twist e w = fun j => phiInv p O (e (fun i => phiR (w i)) j) := rfl

end GlobalTheory.DetInv.Twist

namespace GlobalTheory.DetInv

open Twist in

theorem frame_twist : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ)
    (ψ : RL p O Λ →+* RL p O Λ) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O))
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → IsFrame ρ e →
    ∃ e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O),
      IsFrame (fun l => (ρ l).map (phiInv p O)) e' ∧
        ∀ w, e' (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  intro p _ O _ _ _ Λ _ _ N h ψ ρ e hψ he
  refine ⟨twist e, fun l w => ?_, fun w => ?_⟩
  · rw [twist_apply, twist_apply]
    have h1 : (fun i => phiR ((((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) i)) =
        ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • fun i => phiR (w i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, phiR_one_tmul_mul]
    rw [h1, he]
    funext j
    have := RingHom.map_mulVec (phiInv p O) (ρ l) (e (fun i => phiR (w i))) j
    exact this
  · rw [twist_apply]
    funext j
    simp only [eq_psiR hψ, phiR_psiR]

end GlobalTheory.DetInv
