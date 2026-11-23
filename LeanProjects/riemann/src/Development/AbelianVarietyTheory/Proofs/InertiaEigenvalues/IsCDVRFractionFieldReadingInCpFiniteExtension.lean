import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExt

section Val

open Classical

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_unit' (u : Vˣ) : vV V (algebraMap V K u) = 0 := by
  have : valV V (algebraMap V K u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_irr' {a : V} (ha : Irreducible a) : vV V (algebraMap V K a) = 1 := by
  have : valV V (algebraMap V K a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem vV_pow' {x : K} (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

variable (V K) in

def absOfVal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) : AbsoluteValue K ℝ where
  toFun x := if x = 0 then 0 else c ^ (vV V x)
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, vV_mul hx hy, zpow_add₀ hc0.ne']
  nonneg' x := by
    show 0 ≤ (if x = 0 then 0 else c ^ (vV V x))
    split_ifs
    · exact le_rfl
    · positivity
  eq_zero' x := by
    show (if x = 0 then 0 else c ^ (vV V x)) = 0 ↔ x = 0
    split_ifs with h
    · simp [h]
    · simp [h, zpow_ne_zero _ hc0.ne']
  add_le' x y := by
    show (if x + y = 0 then 0 else c ^ (vV V (x + y))) ≤
      (if x = 0 then 0 else c ^ (vV V x)) + (if y = 0 then 0 else c ^ (vV V y))
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    have px := zpow_pos hc0 (vV V x)
    have py := zpow_pos hc0 (vV V y)
    by_cases hxy : x + y = 0
    · simp only [hxy, hx, hy, if_true, if_false]; positivity
    simp only [hxy, hx, hy, if_false]
    rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith

theorem absOfVal_of_ne (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) {x : K} (hx : x ≠ 0) :
    absOfVal V K c hc0 hc1 x = c ^ (vV V x) := by
  show (if x = 0 then 0 else c ^ (vV V x)) = _
  simp [hx]

end Val

theorem norm_eq_zpow (T : CDVR) {C : Type} [NormedField C] (k : T.Fr →+* C)
    (hball : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x) {π : T.V} (hπ : Irreducible π) (x : T.Fr) (hx : x ≠ 0) :
    ‖k x‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V x := by
  have hu : ∀ u : T.Vˣ, ‖k (algebraMap T.V T.Fr u)‖ = 1 := by
    intro u
    have h1 := (hball (algebraMap T.V T.Fr u)).2 ⟨u, rfl⟩
    have h2 := (hball (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖k (algebraMap T.V T.Fr u)‖ * ‖k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one,
        norm_one]
    nlinarith [norm_nonneg (k (algebraMap T.V T.Fr u)), norm_nonneg (k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ)))]
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hρ0 : ‖k (algebraMap T.V T.Fr π)‖ ≠ 0 := by
    simpa using hπ0
  have key : ∀ a : T.V, a ≠ 0 →
      ‖k (algebraMap T.V T.Fr a)‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V (algebraMap T.V T.Fr a) := by
    intro a ha
    obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu0 : algebraMap T.V T.Fr u ≠ 0 := by simp
    rw [map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hπ0), vV_pow', vV_unit', vV_irr' hπ, map_mul, norm_mul, hu,
      map_pow, norm_pow]
    simp
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap T.V T.Fr b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hv := vV_mul (V := T.V) hx hb1
  rw [div_mul_cancel₀ _ hb1] at hv
  rw [map_div₀, norm_div, key a ha0, key b hb0, ← zpow_sub₀ hρ0, hv]
  congr 1
  ring

theorem isReading_ext : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr),
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  intro p _ F _ _ φ T io k hk T' i hi j hj
  have hji : ∀ y, j (i y) = k y := fun y => by rw [← hj]; rfl
  refine ⟨fun a => by rw [RingHom.comp_apply, hji]; exact hk.comp a, fun x => ?_⟩
  obtain ⟨hfin, r, hr, hv⟩ := hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by simpa using hπ.ne_zero
  set ρ := ‖k (algebraMap T.V T.Fr π)‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 ((map_ne_zero k).2 hπ0)
  have hρ1 : ρ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv'⟩ := (hk.int _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv', map_one, mul_inv_cancel₀ hπ0]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ρ ^ ((1 : ℝ) / r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hρ0 _
  have hc1 : c < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hcr : c ^ r = ρ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  letI NF : NontriviallyNormedField T.Fr :=
    { NormedField.induced T.Fr ℂ_[p] k k.injective with
      non_trivial := ⟨(algebraMap T.V T.Fr π)⁻¹, by
        show 1 < ‖k (algebraMap T.V T.Fr π)⁻¹‖
        rw [map_inv₀, norm_inv]
        exact (one_lt_inv₀ hρ0).2 hρ1⟩ }
  have hnk : ∀ y : T.Fr, ‖y‖ = ‖k y‖ := fun y => rfl
  haveI : IsUltrametricDist T.Fr :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnk, hnk, hnk, map_add]
      exact IsUltrametricDist.norm_add_le_max _ _
  haveI : CompleteSpace T.Fr := Formalism.MainNotions.ExistsIdealDenominator.complete_of_adic (O := T.V) (K := T.Fr) (fun y => hk.int y) inferInstance
  letI := i.toAlgebra
  haveI : FiniteDimensional T.Fr T'.Fr := hfin
  have e1 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := (NormedField.toAbsoluteValue ℂ_[p]).comp j.injective) (fun y => by
      show ‖j (i y)‖ = ‖y‖
      rw [hji, hnk]) x
  have e2 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := absOfVal T'.V T'.Fr c hc0 hc1.le) (fun y => by
      show absOfVal T'.V T'.Fr c hc0 hc1.le (i y) = ‖y‖
      by_cases hy : y = 0
      · subst hy; simp
      rw [absOfVal_of_ne _ _ _ ((map_ne_zero i).2 hy), hv, zpow_mul, zpow_natCast, hcr, hnk,
        norm_eq_zpow T k hk.int hπ y hy]) x
  have hx : ‖j x‖ = absOfVal T'.V T'.Fr c hc0 hc1.le x := e1.trans e2.symm
  rw [hx]
  by_cases hx0 : x = 0
  · subst hx0
    simp only [map_zero, zero_le_one, true_iff]
    exact ⟨0, map_zero _⟩
  rw [absOfVal_of_ne _ _ _ hx0]
  change _ ↔ ∃ a : T'.V, algebraMap T'.V T'.Fr a = x
  rw [GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have := one_lt_zpow_of_neg₀ hc0 hc1 hn
    linarith
  · intro h
    exact zpow_le_one₀ hc0 hc1.le h

end GlobalTheory.GeoTie.ReadExt
