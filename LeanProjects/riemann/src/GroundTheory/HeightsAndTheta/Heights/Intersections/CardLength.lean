import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem card_eq_card_residueField_of_isSimpleModule (N : Type v) [AddCommGroup N] [Module R N]
    [IsSimpleModule R N] : Nat.card N = Nat.card (ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R N›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact Nat.card_congr e.toEquiv

theorem card_eq_pow_of_length_eq (n : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M],
    Module.length R M = n → Nat.card M = Nat.card (ResidueField R) ^ n := by
  induction n with
  | zero =>
    intro M _ _ h
    have : Subsingleton M := Module.length_eq_zero_iff.mp (by exact_mod_cast h)
    rw [pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨0⟩⟩
  | succ n ih =>
    intro M _ _ h
    have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp (by rw [h]; exact ENat.natCast_ne_top _)
    obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
    have hnt : Nontrivial M := Module.length_pos_iff.mp (by rw [h]; exact_mod_cast Nat.succ_pos n)
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
    have hs : IsSimpleModule R N := (isSimpleModule_iff_isAtom).mpr hN
    have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    rw [h, Module.length_eq_one] at hlen
    have hq : Module.length R (M ⧸ N) = n := by
      have hne : Module.length R (M ⧸ N) ≠ ⊤ := by
        intro ht
        rw [ht] at hlen
        exact ENat.natCast_ne_top _ (hlen.trans (add_top _))
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hm] at hlen ⊢
      have : n + 1 = 1 + m := by exact_mod_cast hlen
      congr 1
      omega
    rw [Submodule.card_eq_card_quotient_mul_card N, card_eq_card_residueField_of_isSimpleModule (R := R) N, ih (M ⧸ N) hq,
      pow_succ, mul_comm]

theorem card_eq_card_residueField_pow_length (M : Type v) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    Nat.card M = Nat.card (ResidueField R) ^ (Module.length R M).toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  rw [← hn, ENat.toNat_natCast]
  exact card_eq_pow_of_length_eq n M hn.symm

end GroundTheory.Heights₂.Heights.Inter
