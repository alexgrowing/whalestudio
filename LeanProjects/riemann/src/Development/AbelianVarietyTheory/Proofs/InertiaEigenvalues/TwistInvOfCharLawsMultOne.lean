import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host)
    (χ χ' : D.naut.LP w) (c c' : ℂ)
    (hu : D.naut.unr χ) (hu' : D.naut.unr χ') (hd' : D.naut.lpDim χ' = 1)
    (hc : D.naut.frobEig χ = {c}) (hc' : D.naut.frobEig χ' = {c'}) (h : c * c' = 1) :
    D.naut.lpChar χ χ' = D.naut.lpUnr w {1} := by
  have hu2 := D.naut.unr_char χ χ' hd' hu hu'
  rw [D.naut.unr_eq_lpUnr _ hu2, D.naut.frobEig_char χ χ' c' hu hu' hd' hc', hc]
  simp [h]

open Polynomial NumberField IsDedekindDomain in
private lemma exists_frobEig_etaT_inv_etaTinv (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host) :
    ∃ c : ℂ, c ≠ 0 ∧ D.naut.frobEig (D.naut.locG D.naut.etaT w) = {c} ∧
      D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
  have hu := D.naut.etaT_unr w
  have hcard : (D.naut.frobEig (D.naut.locG D.naut.etaT w)).card = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hne := D.naut.frobEig_ne_zero _ hu
  refine ⟨c, fun h0 => hne (by rw [hc, h0]; exact Multiset.mem_singleton_self 0), hc, ?_⟩
  rw [(D.naut.etaTinv_def w).2, hc]
  simp

open Polynomial NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne :
    ∀ D : _root_.Formalism.BasicNotions.D7, _root_.GlobalTheory.TypeLeaf.CharLaws D → _root_.GlobalTheory.TypeLeaf.MultOne D →
      _root_.GlobalTheory.TypeLeaf.TwistInv D := by
  intro D hlaw hmult
  have hdim : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 :=
    fun w => D.naut.locG_dim _ w
  have hdim' : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 :=
    fun w => D.naut.locG_dim _ w
  constructor
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim w) (hdim' w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c c⁻¹ (D.naut.etaT_unr w)
        (D.naut.etaTinv_def w).1 (hdim' w) hc hc' (mul_inv_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim' w) (hdim w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c (D.naut.etaTinv_def w).1
        (D.naut.etaT_unr w) (hdim w) hc' hc (inv_mul_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]

end GlobalTheory.TypeLeaf
