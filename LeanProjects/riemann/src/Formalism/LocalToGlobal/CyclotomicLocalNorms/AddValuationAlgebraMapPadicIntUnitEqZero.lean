import Mathlib
import Formalism.LocalToGlobal.CyclotomicLocalNorms.FiniteDimensionalUnramifiedSubfield

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Filter Topology
open scoped Classical

variable {l : ℕ} [Fact l.Prime]

theorem modEq_of_pow_eq {k : ℕ} (hk : 0 < k) {ζ : Om l} (hz : IsPrimitiveRoot ζ k) {a b : ℕ}
    (h : ζ ^ a = ζ ^ b) : a ≡ b [MOD k] := by
  obtain ⟨U, rfl⟩ := hz.isUnit hk.ne'
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
    pow_eq_pow_iff_modEq, ← orderOf_units, ← hz.eq_orderOf] at h
  exact h

theorem norm_χZ_sub_le (g : GQ l) (k c : ℕ) (h : ∀ z : Om l, z ^ (l ^ k) = 1 → g z = z ^ c) :
    ‖((χZ l g : ℤ_[l]ˣ) : ℤ_[l]) - (c : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := ζQ_primitive l k
  have h1 := χZ_spec g k (ζQ l k) hz.pow_eq_one
  rw [h _ hz.pow_eq_one] at h1
  have h2 := modEq_of_pow_eq (pow_pos (Fact.out : l.Prime).pos k) hz h1
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h2
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_natCast, ← h2, sub_self]

theorem eq_of_norm_sub_le {x y : ℚ_[l]} (h : ∀ m : ℕ, ‖x - y‖ ≤ (l : ℝ) ^ (-(m : ℤ))) : x = y := by
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hpos
  exact absurd (h k) (not_le.2 hk)

theorem eq_χQ_of_cyc (χ' : GQ l →* ℚ_[l]ˣ)
    (h : ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
      ∃ a : ℕ, ‖(χ' g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a) :
    χ' = χQ l := by
  refine MonoidHom.ext fun g => Units.ext ?_
  apply eq_of_norm_sub_le
  intro m
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := ζQ_primitive l m
  obtain ⟨a, ha, hga⟩ := h g m (ζQ l m) hz.pow_eq_one
  have h1 := norm_χZ_sub_le g m a (fun z hz' => by
    obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hz'
    rw [map_pow, hga, ← pow_mul, ← pow_mul, mul_comm])
  have h2 : ‖(χQ l g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    rw [χQ_coe]
    rw [PadicInt.norm_def] at h1
    push_cast at h1
    exact h1
  have h3 : (χ' g : ℚ_[l]) - (χQ l g : ℚ_[l]) =
      ((χ' g : ℚ_[l]) - (a : ℚ_[l])) - ((χQ l g : ℚ_[l]) - (a : ℚ_[l])) := by ring
  rw [h3, sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans ?_
  rw [norm_neg]
  exact max_le ha h2

theorem χQ_cyc_of (χ' : GQ l →* ℚ_[l]ˣ)
    (h : ∀ g : GQ l, (χ' g : ℚ_[l]) = ((cyclotomicCharacter (Om l) l g.toRingEquiv : ℤ_[l]) : ℚ_[l]))
    (g : GQ l) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    ∃ a : ℕ, ‖(χ' g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a := by
  rw [h g]
  exact χQ_cyc g m ζ hζ

section W

variable {LL : FinExt l}

end W

end Formalism.L2.LocGap.Gal
