import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace RigSymForm

variable {K : Type} [Field K] [Algebra K ℂ] (P : RigSymForm K)

theorem thetaSec_add_latVec {N : ℕ} {f : P.Fn} (hf : f ∈ thetaSec P.pt P.ch N)
    (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : f (w + P.latVec u v) = P.autL N u v w * f w := by
  obtain ⟨-, h1, h2⟩ := hf
  have : w + P.latVec u v = (w + P.pt.τ *ᵥ intVec u) + intVec v := by
    simp only [latVec]; abel
  rw [this, h1, h2, autL]; ring

theorem autL_ne_zero (N : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : P.autL N u v w ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

theorem autL_add (N₁ N₂ : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL (N₁ + N₂) u v w = P.autL N₁ u v w * P.autL N₂ u v w := by
  simp only [autL, ← perFactor_add, ← autFactor_add]; ring

theorem autL_mul (d k : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL (d * k) u v w = P.autL d u v w ^ k := by
  induction k with
  | zero =>
    simp [autL, perFactor, autFactor]
  | succ k ih => rw [Nat.mul_succ, autL_add, ih, pow_succ]

theorem torsAvg_congr {N m : ℕ} {F₁ F₂ : P.Fn} {z : Fin P.g → ℂ}
    (h : ∀ u v : Fin P.g → Fin m, F₁ (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
      F₂ (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) :
    P.torsAvg N m F₁ z = P.torsAvg N m F₂ z := by
  simp only [torsAvg, h]

theorem torsAvg_cechD {N m r : ℕ} (ψ : Finset (Fin (r + 1)) → P.Fn) (J : Finset (Fin (r + 1)))
    (z : Fin P.g → ℂ) :
    cechD (fun I => P.torsAvg N m (ψ I)) J z = P.torsAvg N m (cechD ψ J) z := by
  simp only [cechD, torsAvg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => by ring

theorem torsAvg_div {n d k m : ℕ} {F G Y : P.Fn} {z : Fin P.g → ℂ}
    (hY : ∀ u v : Fin P.g → Fin m, Y (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
      P.autL d (torsIdx u) (torsIdx v) ((m : ℂ) • z) * Y z) (hY0 : Y z ≠ 0)
    (hG : ∀ u v : Fin P.g → Fin m, G (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
      F (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) /
        Y (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) ^ k) :
    P.torsAvg n m G z = P.torsAvg (n + d * k) m F z / Y z ^ k := by
  simp only [torsAvg, hG, hY, mul_div_assoc, Finset.sum_div]
  refine congrArg _ (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)
  rw [autL_add, autL_mul]
  have h1 := P.autL_ne_zero n (torsIdx u) (torsIdx v) ((m : ℂ) • z)
  have h2 := P.autL_ne_zero d (torsIdx u) (torsIdx v) ((m : ℂ) • z)
  field_simp
  ring

theorem torsAvg_pullback {n m : ℕ} (hm : 1 ≤ m) {G : P.Fn} {w : Fin P.g → ℂ}
    (hG : ∀ u v : Fin P.g → Fin m, G (w + P.latVec (torsIdx u) (torsIdx v)) =
      P.autL n (torsIdx u) (torsIdx v) w * G w) :
    P.torsAvg n m (fun z => G ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) = G w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmw : (m : ℂ) • ((m : ℂ)⁻¹ • w) = w := by rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]
  have hterm : ∀ u v : Fin P.g → Fin m,
      (P.autL n (torsIdx u) (torsIdx v) ((m : ℂ) • ((m : ℂ)⁻¹ • w)))⁻¹ *
        G ((m : ℂ) • ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) = G w := by
    intro u v
    rw [← smul_add, hmw, smul_smul, mul_inv_cancel₀ hm0, one_smul, hG,
      ← mul_assoc, inv_mul_cancel₀ (P.autL_ne_zero _ _ _ _), one_mul]
  simp only [torsAvg, hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  have hg := pow_ne_zero P.g hm0
  rw [two_mul, pow_add]
  field_simp

end RigSymForm

end

end GroundTheory.Heights₂.Heights.KeyFormula
