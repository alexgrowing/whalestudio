import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem card_ker_comp_eq {M : Type} [CommGroup M] (f g : M →* M) :
    Nat.card (f.comp g).ker = Nat.card g.ker * Nat.card (g.range.subgroupOf f.ker) := by
  have hle : g.ker ≤ (f.comp g).ker := by
    intro x hx
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
    rw [hx, map_one]
  have h1 := Subgroup.card_mul_index (g.ker.subgroupOf (f.comp g).ker)
  have h2 : (g.ker.subgroupOf (f.comp g).ker).index = Nat.card ((f.comp g).ker.map g) :=
    Subgroup.relIndex_ker _ _
  have h3 : (f.comp g).ker.map g = g.range ⊓ f.ker := by
    rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq]
  have h4 : Nat.card (g.range.subgroupOf f.ker) = Nat.card (g.range ⊓ f.ker : Subgroup M) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, h2, h3, h4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem index_range_comp_mul {M : Type} [CommGroup M] (f g : M →* M) :
    (f.comp g).range.index * Nat.card f.ker * Nat.card g.ker =
      f.range.index * g.range.index * Nat.card (f.comp g).ker := by
  have h1 : (f.comp g).range.index = (g.range ⊔ f.ker).index * f.range.index := by
    rw [MonoidHom.range_comp, Subgroup.index_map]
  have h2 : g.range.relIndex f.ker * (g.range ⊔ f.ker).index = g.range.index := by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  have h3 : Nat.card (g.range.subgroupOf f.ker) * g.range.relIndex f.ker = Nat.card f.ker :=
    Subgroup.card_mul_index _
  rw [h1, card_ker_comp_eq, ← h2, ← h3]
  ring

theorem index_range_ker_pow_succ_endomorphism {M : Type} [CommGroup M] (f : Monoid.End M)
    (hK : Nat.card (MonoidHom.ker f) ≠ 0) (k : ℕ) :
    Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 ∧
    (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) =
      (MonoidHom.range f).index ^ (k + 1) *
        Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  induction k with
  | zero => simpa using hK
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hc : (f ^ (k + 1 + 1) : Monoid.End M) = MonoidHom.comp f (f ^ (k + 1) : Monoid.End M) := by
      rw [pow_succ' f (k + 1)]; rfl
    rw [hc]
    constructor
    · refine (card_ker_comp_eq (M := M) f (f ^ (k + 1) : Monoid.End M)).trans_ne
        (mul_ne_zero ih1 ?_)
      have h3 := Subgroup.card_mul_index
        ((MonoidHom.range (f ^ (k + 1) : Monoid.End M)).subgroupOf (MonoidHom.ker f))
      intro h
      rw [h, zero_mul] at h3
      exact hK h3.symm
    · have h := index_range_comp_mul (M := M) f (f ^ (k + 1) : Monoid.End M)
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ih1)
      generalize (MonoidHom.comp f (f ^ (k + 1) : Monoid.End M)).range.index = A at *
      generalize Nat.card (MonoidHom.comp f (f ^ (k + 1) : Monoid.End M)).ker = B at *
      generalize (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index = C at *
      generalize Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) = D at *
      generalize Nat.card (MonoidHom.ker f) = K at *
      generalize (MonoidHom.range f).index = I at *
      calc A * K ^ (k + 1 + 1) * D = (A * K * D) * K ^ (k + 1) := by ring
        _ = I * B * (C * K ^ (k + 1)) := by rw [h]; ring
        _ = I ^ (k + 1 + 1) * B * D := by rw [ih2]; ring

theorem index_ker_iterate :
    ∀ (M : Type) [CommGroup M] (f : Monoid.End M) (k : ℕ), (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index ≠ 0 → Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 → (MonoidHom.range f).index ≠ 0 ∧ Nat.card (MonoidHom.ker f) ≠ 0 ∧ (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) = (MonoidHom.range f).index ^ (k + 1) * Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  intro M _ f k hI hK
  have hr : MonoidHom.range (f ^ (k + 1) : Monoid.End M) ≤ MonoidHom.range f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(f ^ k : Monoid.End M) x, by rw [pow_succ']; rfl⟩
  have hk : MonoidHom.ker f ≤ MonoidHom.ker (f ^ (k + 1) : Monoid.End M) := by
    intro x hx
    have hx' : f x = 1 := hx
    rw [pow_succ]
    change (f ^ k : Monoid.End M) (f x) = 1
    rw [hx', map_one]
  have hK' : Nat.card (MonoidHom.ker f) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hK (Subgroup.card_dvd_of_le hk)
  exact ⟨ne_zero_of_dvd_ne_zero hI (Subgroup.index_dvd_of_le hr), hK',
    (index_range_ker_pow_succ_endomorphism f hK' k).2⟩

end GlobalTheory.CNorm
