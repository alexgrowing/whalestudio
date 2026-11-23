import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

open Classical in

theorem emb_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    {e : Fin r → Fin n} {ι : GU σ r →* GU σ n} (he : Function.Injective e) (hι : IsEmb e ι)
    (D : Fin n → L) (s : GU σ r) (hs : mat s = Matrix.diagonal (D ∘ e)) :
    mat (ι s) * Matrix.diagonal (fun a => if a ∈ Set.range e then 1 else D a) = Matrix.diagonal D := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ Set.range e
  · rw [if_pos hb, mul_one]
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      rw [(hι s).1, hs]
      simp [Matrix.diagonal_apply, he.eq_iff]
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      rw [(hι s).2 a b (Or.inl ha), Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]
  · rw [if_neg hb, (hι s).2 a b (Or.inr hb)]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab, zero_mul]

theorem embTorus : EmbTorus := by
  classical
  intro L _ _ σ n r e ι he hι D D' t t' s s' ht ht' hs hs' hD
  have h1 := emb_mul_diagonal he hι D s hs
  have h2 := emb_mul_diagonal he hι D' s' hs'
  have hZ : (fun a => if a ∈ Set.range e then (1 : L) else D' a) =
      fun a => if a ∈ Set.range e then (1 : L) else D a := by
    funext a
    by_cases ha : a ∈ Set.range e
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, hD a ha]
  have hz : mat ((ι s)⁻¹ * t) = Matrix.diagonal (fun a => if a ∈ Set.range e then (1 : L) else D a) := by
    rw [mat_mul, ht, ← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨(ι s)⁻¹ * t, by group, ?_, fun g => ?_⟩
  · apply mat_injective
    rw [mat_mul, hz, ← hZ, ht', ← h2]
  · apply mat_injective
    rw [mat_mul, mat_mul (ι g), hz]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · by_cases ha : a ∈ Set.range e
      · by_cases hb : b ∈ Set.range e
        · rw [if_pos ha, if_pos hb, one_mul, mul_one]
        · rw [(hι g).2 a b (Or.inr hb), Matrix.one_apply_ne hab, mul_zero, zero_mul]
      · rw [(hι g).2 a b (Or.inl ha), Matrix.one_apply_ne hab, mul_zero, zero_mul]

end GlobalTheory.SatakeWeyl
