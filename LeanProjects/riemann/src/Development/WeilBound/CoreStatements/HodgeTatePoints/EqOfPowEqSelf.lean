import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Teich

theorem eq_of_pow_eq_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (q : ℕ)
    (hq : (q : IsLocalRing.ResidueField O) = 0) {x y : O} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hgeom := geom_sum₂_mul x y q
  rw [hx, hy] at hgeom
  have hS : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 := by
    have hmul : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) * (x - y) = 1 * (x - y) := by
      rw [hgeom, one_mul]
    exact mul_right_cancel₀ hsub hmul
  have hres := congrArg (IsLocalRing.residue O) hS
  rw [map_sum, map_one] at hres
  simp only [map_mul, map_pow, ← h] at hres
  rw [geom_sum₂_self, hq, zero_mul] at hres
  exact zero_ne_one hres

theorem card_eq_zero {O : Type} [CommRing O] [IsLocalRing O] {F : Type} [Field F] [Fintype F]
    (σ : F →+* IsLocalRing.ResidueField O) :
    ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 := by
  rw [← map_natCast σ, FiniteField.cast_card_eq_zero, map_zero]

theorem exists_lift {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {F : Type} [Field F]
    [Fintype F] (ζ : O) (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (σ : F →+* IsLocalRing.ResidueField O) (a : F) :
    ∃ x : O, x ^ Fintype.card F = x ∧ IsLocalRing.residue O x = σ a := by
  have hQ1 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 := ⟨Fintype.card F - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel] at hζ
  haveI : NeZero m := ⟨by omega⟩
  have hQres := PositivityTheory.HtPt.Teich.card_eq_zero (O := O) σ
  have hfix : ∀ k : ℕ, (ζ ^ k) ^ Fintype.card F = ζ ^ k := by
    intro k
    rw [hm, pow_succ, ← pow_mul, mul_comm k m, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hprim : IsPrimitiveRoot (IsLocalRing.residue O ζ) m := by
    refine ⟨?_, ?_⟩
    · rw [← map_pow, hζ.pow_eq_one, map_one]
    · intro l hl
      apply hζ.dvd_of_pow_eq_one
      apply PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQres (hfix l) (one_pow _)
      rw [map_pow, hl, map_one]
  by_cases ha : a = 0
  · refine ⟨0, zero_pow (by omega), ?_⟩
    rw [ha, map_zero, map_zero]
  · have hpow := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hm, Nat.add_sub_cancel] at hpow
    have h1 : (σ a) ^ m = 1 := by rw [← map_pow, hpow, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, hfix i, by rw [map_pow, hi]⟩

theorem glue_teich : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p := by
  intro O _ _ _ F _ _ p _ _ ζ hζ σ
  have hQ : ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 :=
    PositivityTheory.HtPt.Teich.card_eq_zero σ
  have huniq : ∀ {x y : O}, x ^ Fintype.card F = x → y ^ Fintype.card F = y →
      IsLocalRing.residue O x = IsLocalRing.residue O y → x = y :=
    fun hx hy h => PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQ hx hy h
  have hfixχ : ∀ (χ : F →*₀ O) (a : F), χ a ^ Fintype.card F = χ a := fun χ a => by
    rw [← map_pow, FiniteField.pow_card]
  refine ⟨?_, ?_⟩
  · choose L hL hLres using PositivityTheory.HtPt.Teich.exists_lift ζ hζ σ
    let χ : F →*₀ O :=
      { toFun := L
        map_zero' := huniq (hL 0) (zero_pow Fintype.card_ne_zero) (by rw [hLres, map_zero, map_zero])
        map_one' := huniq (hL 1) (one_pow _) (by rw [hLres, map_one, map_one])
        map_mul' := fun a b => huniq (hL (a * b)) (by rw [mul_pow, hL a, hL b])
          (by rw [hLres, map_mul, map_mul, hLres, hLres]) }
    refine ⟨χ, hLres, fun χ' hχ' => ?_⟩
    exact MonoidWithZeroHom.ext fun a => huniq (hfixχ χ' a) (hL a) ((hχ' a).trans (hLres a).symm)
  · intro σ' χ χ' hσ' hχ hχ' a
    refine huniq (hfixχ χ' a) (by rw [← pow_mul, mul_comm p, pow_mul, hfixχ χ a]) ?_
    rw [hχ', hσ', map_pow, hχ]

end PositivityTheory.HtPt.Teich
