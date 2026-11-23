import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.redRoot :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M : ℕ) (ζ : R),
    p.Coprime M → IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M ∧ M ∣ p - 1 := by
  intro R _ _ p hp π M ζ hcop hζ
  have hpp : p.Prime := hp.out
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · exact absurd (Nat.coprime_zero_right p |>.mp hcop) hpp.one_lt.ne'
    · exact h
  have hne : NeZero (M : ZMod p) := by
    refine ⟨fun h => ?_⟩
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hroot : (Polynomial.cyclotomic M R).IsRoot ζ := hζ.isRoot_cyclotomic hM
  have hroot' : (Polynomial.cyclotomic M (ZMod p)).IsRoot (π ζ) := by
    rw [← Polynomial.map_cyclotomic M π]
    exact hroot.map
  have hprim : IsPrimitiveRoot (π ζ) M := (Polynomial.isRoot_cyclotomic_iff).mp hroot'
  refine ⟨hprim, hprim.dvd_of_pow_eq_one _ ?_⟩
  exact ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hM.ne')
