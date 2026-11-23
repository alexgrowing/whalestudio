import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.isAdicComplete_of_pow_le_of_pow_le (A : Type) [CommRing A] (J J' : Ideal A) (k l : ℕ)
    (h1 : J ^ k ≤ J') (h2 : J' ^ l ≤ J) (h : IsAdicComplete J A) : IsAdicComplete J' A := by
  have hk : J ^ (k + 1) ≤ J' := le_trans (Ideal.pow_le_pow_right (Nat.le_succ k)) h1
  have hl : J' ^ (l + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ l)) h2
  have hJ : ∀ m, J ^ ((k + 1) * m) ≤ J' ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hk m
  have hJ' : ∀ m, J' ^ ((l + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hl m
  exact
    { haus' := fun x hx => h.toIsHausdorff.haus' x fun m =>
        (hx ((l + 1) * m)).mono (Submodule.smul_mono_left (hJ' m))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun m => f ((l + 1) * m))
          (fun {m n} hmn => (hf (Nat.mul_le_mul_left (l + 1) hmn)).mono
            (Submodule.smul_mono_left (hJ' m)))
        refine ⟨L, fun n => ?_⟩
        have hn : n ≤ (l + 1) * ((k + 1) * n) :=
          (Nat.le_mul_of_pos_left n (Nat.succ_pos k)).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos l))
        exact (hf hn).trans ((hL ((k + 1) * n)).mono (Submodule.smul_mono_left (hJ n))) }

end GlobalTheory
