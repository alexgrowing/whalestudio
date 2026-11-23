import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix
open scoped ComplexConjugate

theorem norm_letter_scal (σ : ℂ) (b : Bool) : ‖(if b then σ else conj σ)‖ = ‖σ‖ := by
  cases b <;> simp

theorem uInv_ccle {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (σ : ℂ)
    (hσ : ‖σ‖ ≤ 2) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → E) (c : ℝ), (∀ e, B.CCle A m (x e) c) →
      ∀ e, B.CCle A m (KB.uInv σ w x e) (3 ^ w.length * c) ∧
        B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c)
  | [], x, c, hx, e => by
    have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
    refine ⟨by simpa [KB.uInv] using hx e, ?_⟩
    simp only [KB.uInv, sub_self, List.length_nil, pow_zero, one_mul]
    exact JCx2.pd_ccle_mono_c BetaSesquilinearity.CCle_zero (by positivity)
  | l :: w, x, c, hx, e => by
    have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
    have ih0 := uInv_ccle A m σ hσ w (fun e' => x (Fin.cons (0 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
    have ih1 := uInv_ccle A m σ hσ w (fun e' => x (Fin.cons (1 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
    have hs : ‖(if l.1 then σ else conj σ)‖ = ‖σ‖ := norm_letter_scal σ l.1
    have h3 : (0 : ℝ) ≤ 3 ^ w.length := by positivity
    have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
    have hlen : (l :: w).length = w.length + 1 := rfl
    have hce : e = Fin.cons (e 0) (fun a => e a.succ) := (Fin.cons_self_tail e).symm
    have hp : (3 : ℝ) ^ (l :: w).length = 3 * 3 ^ w.length := by rw [hlen, pow_succ, mul_comm]
    simp only [KB.uInv]
    by_cases he : e 0 = 0
    · rw [if_pos he]
      have hxe : x e = x (Fin.cons (0 : Fin 2) (fun a => e a.succ)) := by
        conv_lhs => rw [hce, he]
      refine ⟨JCx2.pd_ccle_mono_c ih0.1 (by rw [hp]; nlinarith), ?_⟩
      rw [hxe]
      exact JCx2.pd_ccle_mono_c ih0.2 (by rw [hp]; nlinarith [mul_nonneg h3 hσ0])
    · rw [if_neg he]
      have he1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h he
        · exact h
      have hxe : x e = x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) := by
        conv_lhs => rw [hce, he1]
      refine ⟨?_, ?_⟩
      · have := BetaSesquilinearity.CCle_add ih1.1 (BetaSesquilinearity.CCle_smul (if l.1 then σ else conj σ) ih0.1)
        rw [hs] at this
        exact JCx2.pd_ccle_mono_c (show B.CCle A m ((KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ)) +
          (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) _ from this)
          (by rw [hp]; nlinarith [mul_nonneg h3 hc])
      · have := BetaSesquilinearity.CCle_add ih1.2 (BetaSesquilinearity.CCle_smul (if l.1 then σ else conj σ) ih0.1)
        rw [hs] at this
        rw [hxe]
        have hf : (fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
            (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) g -
            x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) =
            fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) g -
              x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) +
              (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) g := by
          funext g
          simp only [Pi.add_apply, Pi.smul_apply]
          abel
        rw [hf]
        exact JCx2.pd_ccle_mono_c this (by rw [hp]; nlinarith [mul_nonneg h3 hc, mul_nonneg (mul_nonneg h3 hσ0) hc])

end Formalism.FourierDecayAlt.P.StandardPairingDecay
