import Mathlib
import Formalism.PeriodIntegrals.GZeroLogBound

noncomputable section

namespace PI.GZeroLogBound.UnitaryGroupMassFormula

open Formalism.BasicNotions

theorem card_GL_le (r g : ℕ) [NeZero g] :
    Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r * r) := by
  have h1 : Nat.card (GL (Fin r) (ZMod g)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  have h2 : Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) = g ^ (r * r) := by
    show Nat.card (Fin r → Fin r → ZMod g) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, ← pow_mul]
  omega

theorem zero_log_bound (D : D7) : PI.GZeroLogBound.Conclusion0 D := by
  intro Y hY
  unfold lam0
  have hg2 : ∀ k, 2 ≤ D.host.g k := fun k => (D.host.g_prime k).two_le
  have hY2 : (2 : ℝ) ≤ 2 * Y := le_trans (by exact_mod_cast hg2 0) (hY 0)
  have hpos : (0 : ℝ) < 2 * Y := by linarith
  have hk : ∀ k, ((Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℕ) : ℝ) ^ D.R.f ≤
      ((2 * Y) ^ (D.R.r * D.R.r)) ^ D.R.f := by
    intro k
    have : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    apply pow_le_pow_left₀ (by positivity)
    calc ((Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℕ) : ℝ)
        ≤ ((D.host.g k : ℕ) : ℝ) ^ (D.R.r * D.R.r) := by
          exact_mod_cast card_GL_le D.R.r (D.host.g k)
      _ ≤ (2 * Y) ^ (D.R.r * D.R.r) := pow_le_pow_left₀ (by positivity) (hY k) _
  have hbound : (D.what₂.restRowsFiniteGroupCard : ℝ) ≤ (2 * Y) ^ (2 * D.R.f * D.R.r ^ 2) := by
    rw [D.nd.restN_card_levelGroup_eq]
    push_cast
    rw [Fin.prod_univ_two]
    calc _ ≤ ((2 * Y) ^ (D.R.r * D.R.r)) ^ D.R.f * ((2 * Y) ^ (D.R.r * D.R.r)) ^ D.R.f :=
          mul_le_mul (hk 0) (hk 1) (by positivity) (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have hc : (0 : ℝ) < D.what₂.restRowsFiniteGroupCard := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos
  calc Real.log (D.what₂.restRowsFiniteGroupCard) ≤ Real.log ((2 * Y) ^ (2 * D.R.f * D.R.r ^ 2)) :=
        Real.log_le_log hc hbound
    _ = _ := by rw [Real.log_pow]; push_cast; ring

theorem target : PI.GZeroLogBound.Target := fun D => zero_log_bound D

end PI.GZeroLogBound.UnitaryGroupMassFormula
