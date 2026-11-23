import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadicStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_phiInv (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_ofPadic' (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  ext n
  simp only [phiInv, ofPadic, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem frob_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  conv_lhs => rw [← phiInv_ofPadic' c]
  exact frob_phiInv _

def frobT (G : PDivGroup p O) (y : TDual G) : TDual G where
  toFun t := WittVector.frobenius (y t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, frob_ofPadic, smul_eq_mul]

def xiPhiInvT (ε : PreTilt O p) (G : PDivGroup p O) (m : TDual G) : TDual G where
  toFun t := xi ε * phiInv p O (m t)
  map_add' s t := by rw [map_add, map_add, mul_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, phiInv_ofPadic', smul_eq_mul, mul_left_comm]

def frobLatt (G : PDivGroup p O) :
    latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G where
  toFun y := ⟨frobT G y.1, fun n => by
    obtain ⟨x, hx⟩ := y.2 (n + 1)
    exact ⟨x, fun t => by rw [← hx]; rfl⟩⟩
  map_add' y z := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((y.1 + z.1) t) = _
    rw [LinearMap.add_apply, map_add]; rfl
  map_smul' a y := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((a • y.1) t) = _
    rw [LinearMap.smul_apply, smul_eq_mul, map_mul]; rfl

end GlobalTheory.PDivLat.Frob

open GlobalTheory.PDivLat.Frob in

theorem GlobalTheory.PDivLat.exists_frobenius_latt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  obtain ⟨-, -, -, h0, hs, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  refine ⟨fun G => frobLatt G, fun G y t => rfl, fun G m => ?_⟩
  refine ⟨⟨xiPhiInvT ε G m.1, fun n => ?_⟩, ?_⟩
  · cases n with
    | zero => exact ⟨0, fun t => by
        show ghost p O 0 (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, h0, zero_mul, LinearMap.zero_apply]⟩
    | succ k =>
      obtain ⟨x, hx⟩ := m.2 k
      exact ⟨(p : O) • x, fun t => by
        show ghost p O (k + 1) (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, hs, hphi, hx, LinearMap.smul_apply, smul_eq_mul]⟩
  · apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius (xi ε * phiInv p O (m.1 t)) = _
    rw [map_mul, frob_phiInv]; rfl
