import Mathlib
open PowerSeries

namespace GlobalTheory

open IsLocalRing Polynomial in

theorem exists_isPrimitiveRoot_sub_isUnit_of_dvd_sub_one {l : ℕ} {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hl : l.Prime) (hu : ¬ IsUnit (l : O)) (e : ℕ) (he : e ∣ l - 1) :
    ∃ ω : O, IsPrimitiveRoot ω e ∧
      ∀ i j : ℕ, i < e → j < e → i ≠ j → IsUnit (ω ^ i - ω ^ j) := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  have he0 : e ≠ 0 := by rintro rfl; exact hl1 (zero_dvd_iff.1 he)
  have hel : e < l := by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hl1) he; omega

  have hlk : ((l : ℕ) : ResidueField O) = 0 := by
    have h : residue O (l : O) = 0 := (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
    simpa using h
  have : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 hlk

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hg' : IsPrimitiveRoot g (l - 1) := by
    have h := IsPrimitiveRoot.orderOf g
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units] at h
  have hd : (l - 1) / e ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hl1) he) (Nat.pos_of_ne_zero he0)).ne'
  have hζ : IsPrimitiveRoot ((g ^ ((l - 1) / e) : (ZMod l)ˣ) : ZMod l) e := by
    have h := hg'.pow_of_dvd hd (Nat.div_dvd_of_dvd he)
    rw [Nat.div_div_self he hl1] at h
    exact IsPrimitiveRoot.coe_units_iff.2 h
  have hζk := hζ.map_of_injective (f := ZMod.castHom (dvd_refl l) (ResidueField O))
    (RingHom.injective _)
  obtain ⟨ω₀, hω₀⟩ := residue_surjective
    (ZMod.castHom (dvd_refl l) (ResidueField O) ((g ^ ((l - 1) / e) : (ZMod l)ˣ) : ZMod l))
  rw [← hω₀] at hζk

  have heu : IsUnit (e : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) ((CharP.cast_eq_zero_iff _ l e).1 h)
    omega
  have hω₀u : IsUnit ω₀ := (residue_ne_zero_iff_isUnit _).1 (hζk.ne_zero he0)
  obtain ⟨ω, hroot, hsub⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ e - Polynomial.C 1 : O[X]) (monic_X_pow_sub_C 1 he0) ω₀
    (by
      rw [← residue_eq_zero_iff]
      simp [hζk.pow_eq_one])
    (by
      have h : IsUnit ((e : O) * ω₀ ^ (e - 1)) := heu.mul (hω₀u.pow _)
      simpa [derivative_X_pow] using h.map (Ideal.Quotient.mk (maximalIdeal O)))
  have hres : residue O ω = residue O ω₀ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsub
  have hωe : ω ^ e = 1 := by
    have h := hroot.eq_zero
    simpa [sub_eq_zero] using h
  refine ⟨ω, ⟨hωe, fun k hk => hζk.dvd_of_pow_eq_one k ?_⟩, fun i j hi hj hij => ?_⟩
  · rw [← hres, ← map_pow, hk, map_one]
  · rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres, sub_ne_zero]
    exact fun h => hij (hζk.pow_inj hi hj h)

end GlobalTheory
