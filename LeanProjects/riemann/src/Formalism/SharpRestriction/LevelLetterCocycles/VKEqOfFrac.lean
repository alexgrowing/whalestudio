import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants

noncomputable section

namespace Formalism.MainNotions.TwOe

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']

private theorem exists_ne_zero_addVal_algebraMap_eq_mul (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ y : R, IsDiscreteValuationRing.addVal R' (algebraMap R R' y) =
      (e : ℕ∞) * IsDiscreteValuationRing.addVal R y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have h0 : algebraMap R R' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap R R' ϖ) := by
    intro hu
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
      (IsLocalRing.maximalIdeal R')
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hmem : ϖ ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := by
      rw [heq]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hu
  have he : e ≠ 0 := by
    rintro rfl
    apply hnu
    rw [hw, pow_zero, mul_one]
    exact w.isUnit
  refine ⟨e, he, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, AddValuation.map_zero, AddValuation.map_zero, ENat.mul_top (by exact_mod_cast he)]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    rw [IsDiscreteValuationRing.addVal_def y u hϖ n hu]
    have hy' : algebraMap R R' y =
        ↑(Units.map (algebraMap R R' : R →* R') u * w ^ n) * ϖ' ^ (e * n) := by
      rw [hu, map_mul, map_pow, hw]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
      ring
    rw [IsDiscreteValuationRing.addVal_def _ _ hϖ' _ hy']
    push_cast
    ring

theorem nval_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) (x : R) :
    nval R' l (algebraMap R R' x) = nval R l x := by
  obtain ⟨e, he, hE⟩ := exists_ne_zero_addVal_algebraMap_eq_mul hinj
  simp only [nval]
  rw [hE x, ← map_natCast (algebraMap R R') l, hE]
  simp only [ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

private theorem nval_mul_eq_add_of_ne_zero (l : ℕ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    nval R l (a * b) = nval R l a + nval R l b := by
  simp only [nval]
  rw [(IsDiscreteValuationRing.addVal R).map_mul, ENat.toNat_add, Nat.cast_add, add_div]
  · exact fun h => ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  · exact fun h => hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)

theorem vK_eq_of_frac (l : ℕ) {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) :
    vK R l x = nval R l a - nval R l b := by
  have key : vK R l x = nval R l (IsLocalization.surj (nonZeroDivisors R) x).choose.1 -
      nval R l ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R) := rfl
  have hspec := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  rw [key]
  generalize (IsLocalization.surj (nonZeroDivisors R) x).choose = q at hspec ⊢
  rcases q with ⟨c, d, hd⟩
  dsimp only at hspec ⊢
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hinjK := IsFractionRing.injective R (FractionRing R)
  have hb' : algebraMap R (FractionRing R) b ≠ 0 := fun h0 => hb (hinjK (by rw [h0, map_zero]))
  have hd' : algebraMap R (FractionRing R) d ≠ 0 := fun h0 => hd0 (hinjK (by rw [h0, map_zero]))
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact mul_ne_zero hx hb' h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hspec
    exact mul_ne_zero hx hd' hspec
  have hcross : a * d = c * b := by
    apply hinjK
    rw [map_mul, map_mul, ← h, ← hspec]
    ring
  have e1 := nval_mul_eq_add_of_ne_zero (R := R) l ha hd0
  have e2 := nval_mul_eq_add_of_ne_zero (R := R) l hc hb
  rw [hcross] at e1
  linarith

abbrev fracMap (hinj : Function.Injective (algebraMap R R')) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (j := algebraMap R R') hinj

theorem vK_map (hinj : Function.Injective (algebraMap R R')) [Module.Finite R R'] (l : ℕ) {x : FractionRing R}
    (hx : x ≠ 0) : vK R' l (fracMap hinj x) = vK R l x := by
  have key : vK R l x = nval R l (IsLocalization.surj (nonZeroDivisors R) x).choose.1 -
      nval R l ((IsLocalization.surj (nonZeroDivisors R) x).choose.2 : R) := rfl
  have hspec := (IsLocalization.surj (nonZeroDivisors R) x).choose_spec
  rw [key]
  generalize (IsLocalization.surj (nonZeroDivisors R) x).choose = q at hspec ⊢
  rcases q with ⟨c, d, hd⟩
  dsimp only at hspec ⊢
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hfx : fracMap hinj x ≠ 0 := fun h0 => hx ((fracMap hinj).injective (by rw [h0, map_zero]))
  have hd' : algebraMap R R' d ≠ 0 := fun h0 => hd0 (hinj (by rw [h0, map_zero]))
  have hcomm : ∀ r : R, fracMap hinj (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (algebraMap R R' r) := fun r => IsLocalization.map_eq _ _
  have hmap : fracMap hinj x * algebraMap R' (FractionRing R') (algebraMap R R' d) =
      algebraMap R' (FractionRing R') (algebraMap R R' c) := by
    rw [← hcomm, ← hcomm, ← map_mul, hspec]
  rw [vK_eq_of_frac l hfx hd' hmap, nval_map hinj l c, nval_map hinj l d]

end Formalism.MainNotions.TwOe

end
