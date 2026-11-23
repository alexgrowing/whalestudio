import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt

noncomputable section

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section aux

variable {F : Type} [CommRing F] {k : ℕ}

def StrictUp (d : ℕ) (A : Matrix (Fin k) (Fin k) F) : Prop :=
  ∀ i j : Fin k, j.val < i.val + d → A i j = 0

theorem strictUp_mul {d : ℕ} {A B : Matrix (Fin k) (Fin k) F} (hA : StrictUp d A)
    (hB : StrictUp 1 B) : StrictUp (d + 1) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < i.val + d
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem strictUp_pow {A : Matrix (Fin k) (Fin k) F} (hA : StrictUp 1 A) (d : ℕ) :
    StrictUp d (A ^ d) := by
  induction d with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    subst h
    omega
  | succ d ih =>
    rw [pow_succ]
    exact strictUp_mul ih hA

theorem strictUp_pow_eq_zero {A : Matrix (Fin k) (Fin k) F} (hA : StrictUp 1 A) {d : ℕ}
    (hd : k ≤ d) : A ^ d = 0 := by
  ext i j
  exact strictUp_pow hA d i j (by have := j.isLt; omega)

theorem isUnitri_one : IsUnitri (1 : Matrix (Fin k) (Fin k) F) :=
  ⟨fun _ _ hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isUnitri_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) (hB : IsUnitri B) :
    IsUnitri (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l < i
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hij (not_lt.mp hl)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hB.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem isUnitri_pow {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) (d : ℕ) :
    IsUnitri (A ^ d) := by
  induction d with
  | zero => rw [pow_zero]; exact isUnitri_one
  | succ d ih => rw [pow_succ]; exact isUnitri_mul ih hA

theorem strictUp_sub_one {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) :
    StrictUp 1 (A - 1) := by
  intro i j hij
  rw [Matrix.sub_apply]
  rcases Nat.lt_or_ge j.val i.val with h | h
  · have h' : j < i := h
    rw [hA.1 i j h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
  · have h' : i = j := Fin.ext (by omega)
    subst h'
    rw [hA.2 i, Matrix.one_apply_eq, sub_self]

theorem isUnitri_pow_char (g : ℕ) [Fact g.Prime] [CharP F g] [Nontrivial F]
    {A : Matrix (Fin k) (Fin k) F} (hA : IsUnitri A) : A ^ (g ^ k) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Subsingleton.elim _ _
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have h1 : (A - 1) ^ (g ^ k) = A ^ (g ^ k) - 1 ^ (g ^ k) :=
      sub_pow_char_pow_of_commute (h := Commute.one_right A) ..
    have h2 : (A - 1) ^ (g ^ k) = 0 :=
      strictUp_pow_eq_zero (strictUp_sub_one hA)
        (le_of_lt (Nat.lt_pow_self (Fact.out : g.Prime).one_lt))
    rw [h2, one_pow] at h1
    exact (sub_eq_zero.mp h1.symm)

end aux

theorem idxFacts : IdxFacts := by
  refine ⟨fun g k hg => ?_, ?_⟩
  · have : Fact g.Prime := ⟨hg⟩
    have hpow : ∀ x : GL (Fin k) (ZMod g), IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g)) →
        x ^ (g ^ k) = 1 := by
      intro x hx
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact isUnitri_pow_char g hx
    let U : Subgroup (GL (Fin k) (ZMod g)) :=
      { carrier := {x | IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g))}
        mul_mem' := fun {a b} ha hb => by
          show IsUnitri ((a * b : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g))
          rw [Units.val_mul]
          exact isUnitri_mul ha hb
        one_mem' := by
          show IsUnitri ((1 : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g))
          rw [Units.val_one]
          exact isUnitri_one
        inv_mem' := fun {a} ha => by
          show IsUnitri ((a⁻¹ : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g))
          have hpos : 0 < g ^ k := pow_pos hg.pos k
          have h1 : a ^ (g ^ k - 1) * a = 1 := by
            rw [← pow_succ, Nat.sub_add_cancel hpos]
            exact hpow a ha
          have h2 : a⁻¹ = a ^ (g ^ k - 1) := (eq_inv_of_mul_eq_one_left h1).symm
          rw [h2, Units.val_pow_eq_pow_val]
          exact isUnitri_pow ha _ }
    have hmem : ∀ x, x ∈ U ↔ IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g)) := fun x => Iff.rfl
    have hcard : Nat.card U =
        Nat.card {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} := rfl
    have hUpos : 0 < Nat.card U := Nat.card_pos
    have hidx : U.index * Nat.card U = Nat.card (GL (Fin k) (ZMod g)) := U.index_mul_card
    refine ⟨U, hmem, ?_, ?_, fun x hx => ⟨k, hpow x hx⟩⟩
    · unfold idxColLoc idxLoc
      rw [← hcard, ← hidx, Nat.cast_mul, mul_div_assoc, div_self, mul_one]
      exact_mod_cast hUpos.ne'
    · exact Nat.pos_of_ne_zero U.index_ne_zero_of_finite
  · intro G X _ _ _ _ hfree
    classical
    have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X), Nat.card_sigma]
    refine Finset.dvd_sum fun ω _ => ?_
    have hb : MulAction.stabilizer G ω.out = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      exact Subgroup.mem_bot.mpr (hfree _ a (MulAction.mem_stabilizer_iff.mp ha))
    rw [hb]
    have : Nat.card (G ⧸ (⊥ : Subgroup G)) = Nat.card G := Subgroup.index_bot
    rw [this]

end Formalism.MainNotions.Gaps.MI
