import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PsiPhi

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_phiInv' (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p _

theorem phiInv_frobenius' (a : Ainf p O) : phiInv p O (WittVector.frobenius a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_apply_frobenius (PreTilt O p) p _

theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

theorem frobenius_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  have key : (_root_.frobenius (PreTilt O p) p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

def phiInvAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { phiInv p O with commutes' := fun c => phiInv_ofPadic c }

def frobAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { (WittVector.frobenius : Ainf p O →+* Ainf p O) with commutes' := fun c => frobenius_ofPadic c }

end GlobalTheory.DetInv.PsiPhi

namespace GlobalTheory.DetInv

open PsiPhi in

theorem psi_phi_tensor : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ],
    (∀ c : ℤ_[p], phiInv p O (ofPadic p O c) = ofPadic p O c) ∧ Function.Bijective (phiInv p O) ∧
    ∃ ψ φ : RL p O Λ →+* RL p O Λ, IsPsi ψ ∧
      (∀ (a : Ainf p O) (l : Λ), φ (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l) ∧
      (∀ r, φ (ψ r) = r) ∧ ∀ r, ψ (φ r) = r := by
  intro p _ O _ _ _ Λ _ _
  refine ⟨fun c => phiInv_ofPadic c,
    Function.bijective_iff_has_inverse.mpr ⟨WittVector.frobenius, frobenius_phiInv', phiInv_frobenius'⟩,
    (Algebra.TensorProduct.map (phiInvAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom,
    (Algebra.TensorProduct.map (frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom,
    fun a l => rfl, fun a l => rfl, ?_, ?_⟩
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      change (frobAlg (phiInvAlg a)) ⊗ₜ l = a ⊗ₜ l
      exact congrArg (· ⊗ₜ[ℤ_[p]] l) (frobenius_phiInv' a)
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      change (phiInvAlg (frobAlg a)) ⊗ₜ l = a ⊗ₜ l
      exact congrArg (· ⊗ₜ[ℤ_[p]] l) (phiInv_frobenius' a)
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

end GlobalTheory.DetInv
