import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

def MoveDefInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ),
      0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
      markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ

namespace MoveEx

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

theorem sig_one (v : InfinitePlace (ex 1 one_ne_zero).F) : sigPosH ((ex 1 one_ne_zero).gram_herm v) = 1 :=
  (sigPos_Hc 1 v.embedding).trans (by simp)

theorem form_one (v : InfinitePlace (ex 1 one_ne_zero).F) (x : Fin 1 → ℂ) :
    (star x ⬝ᵥ ((ex 1 one_ne_zero).gram v *ᵥ x)).re = ‖x 0‖ ^ 2 := by
  suffices h : ∀ τ : QI →+* ℂ, (star x ⬝ᵥ (gramAt (Hc 1) τ *ᵥ x)).re = ‖x 0‖ ^ 2 from h v.embedding
  intro τ
  have h1 : τ 1 = 1 := map_one _
  simp only [gramAt, Hc, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Rat.cast_one, Pi.star_apply]
  rw [h1, one_mul, Complex.star_def, Complex.conj_mul']
  norm_cast

def dPairOne : DPair (ex 1 one_ne_zero) where
  β := exPair.β
  γ := exPair.γ
  c := exPair.c
  sym := exPair.sym
  sim := exPair.sim
  reg := exPair.reg
  trivAf := exPair.trivAf
  posR := fun v x hx => by
    refine ⟨fun _ => ?_, fun h => absurd (sig_one v) h⟩
    have e : exPair.β = 1 := rfl
    rw [e, inv_one, Units.val_one, map_one, Matrix.mul_one]
    have := form_one v x
    refine lt_of_lt_of_eq ?_ this.symm
    have h0 : x (0 : Fin 1) ≠ 0 := fun h => hx (funext fun i => by
      have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      rw [hi]; exact h)
    positivity

end MoveEx

end GlobalTheory.LKDef
