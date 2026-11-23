import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.PlaceLocalRing

section

variable {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {O : Type} [CommRing O] {β : O →+* K}

theorem exists_unit (hinj : Function.Injective β) (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {x : K} (hx : la.valuation K x = 1) : ∃ u : Oˣ, β u = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨a, ha⟩ := (hr x).2 hx.le
  obtain ⟨c, hc⟩ := (hr x⁻¹).2 (by rw [map_inv₀, hx, inv_one])
  have : IsUnit a := IsUnit.of_mul_eq_one c (hinj (by rw [map_mul, ha, hc, mul_inv_cancel₀ hx0, map_one]))
  exact ⟨this.unit, ha⟩

theorem exists_unit_mul_zpow (hinj : Function.Injective β) (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {p : K} (hp : la.valuation K p = WithZero.exp (-1 : ℤ)) {x : K} (hx : x ≠ 0) :
    ∃ u : Oˣ, x = β u * p ^ vLa la x := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hv : la.valuation K x ≠ 0 := by simpa using hx
  obtain ⟨u, hu⟩ := exists_unit hinj hr (x := x * p ^ (-vLa la x)) (by
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul, ← WithZero.exp_log hv, ← WithZero.exp_add]
    simp [vLa])
  refine ⟨u, ?_⟩
  rw [hu, mul_assoc, ← zpow_add₀ hp0]
  simp

theorem vLa_nonneg (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) {a : O} (ha : β a ≠ 0) :
    0 ≤ vLa la (β a) := by
  have hv : la.valuation K (β a) ≠ 0 := by simpa using ha
  have h := (hr _).1 ⟨a, rfl⟩
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  simp only [vLa]
  omega

theorem irreducible_of_valuation (hinj : Function.Injective β)
    (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {π : O} (hp : la.valuation K (β π) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hle : ∀ a : O, la.valuation K (β a) ≤ 1 := fun a => (hr _).1 ⟨a, rfl⟩
  have hun : ∀ a : O, la.valuation K (β a) = 1 → IsUnit a := fun a ha => by
    obtain ⟨u, hu⟩ := exists_unit hinj hr ha
    exact hinj hu ▸ u.isUnit
  refine ⟨fun h => ?_, fun a c h => ?_⟩
  · obtain ⟨c, hc⟩ := h.exists_right_inv
    have h1 : la.valuation K (β π) * la.valuation K (β c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
      calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
        _ ≤ la.valuation K (β π) * 1 := by gcongr; exact hle c
        _ = _ := by rw [mul_one, hp]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    omega
  · rw [h, map_mul, map_mul] at hp
    have h0 := mul_ne_zero_iff.1 (hp.trans_ne WithZero.exp_ne_zero)
    have ha := hle a
    have hc := hle c
    rw [← WithZero.exp_log h0.1, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [← WithZero.exp_log h0.2, ← WithZero.exp_zero, WithZero.exp_le_exp] at hc
    rw [← WithZero.exp_log h0.1, ← WithZero.exp_log h0.2, ← WithZero.exp_add, WithZero.exp_inj] at hp
    by_cases h1 : WithZero.log (la.valuation K (β a)) = 0
    · exact Or.inl (hun a (by rw [← WithZero.exp_log h0.1, h1, WithZero.exp_zero]))
    · exact Or.inr (hun c (by
        rw [← WithZero.exp_log h0.2, show WithZero.log (la.valuation K (β c)) = 0 by omega, WithZero.exp_zero]))

end

theorem dvr_and_overLa : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (O : Type) [CommRing O] (β : O →+* K), Function.Injective β → (∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) → ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), (letI := β.toAlgebra; IsFractionRing O K) ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b → (algebraMap T.V T.Fr).comp b = io.comp β → ∃ e : ℕ, OverLa la T.V io e := by
  intro K _ _ la O _ β hinj hr
  obtain ⟨p, hp⟩ := la.valuation_exists_uniformizer K
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨π, rfl⟩ := (hr p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hπ := irreducible_of_valuation hinj hr hp
  have hdom : IsDomain O := hinj.isDomain β
  have hdvr : IsDiscreteValuationRing O :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hπ, fun {x} hx => by
      have hx' : β x ≠ 0 := (map_ne_zero_iff β hinj).2 hx
      obtain ⟨u, hu⟩ := exists_unit_mul_zpow hinj hr hp hx'
      have h0 := vLa_nonneg hr hx'
      refine ⟨(vLa la (β x)).toNat, u, hinj ?_⟩
      rw [map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg h0, mul_comm, ← hu]⟩
  refine ⟨hdom, hdvr, ?_, ?_⟩
  · letI := β.toAlgebra
    haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).2 hinj
    refine IsFractionRing.of_field O K fun x => ?_
    rcases le_total (la.valuation K x) 1 with h | h
    · obtain ⟨a, ha⟩ := (hr x).2 h
      exact ⟨a, 1, by rw [map_one, div_one]; exact ha.symm⟩
    · obtain ⟨a, ha⟩ := (hr x⁻¹).2 (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h)
      exact ⟨1, a, by rw [map_one, one_div]; change x = (β a)⁻¹; rw [ha, inv_inv]⟩
  · intro T io b hb hc
    have hc' : ∀ a, io (β a) = algebraMap T.V T.Fr (b a) := fun a => (RingHom.congr_fun hc a).symm
    have hlt : valV T.V (io (β π)) < 1 := by
      rw [hc']
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 fun h => hπ.not_isUnit (isUnit_of_map_unit b _ h)
    have hne : valV T.V (io (β π)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hp0)
    have hpos : 0 < vV T.V (io (β π)) := by
      rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      simp only [vV]
      omega
    refine ⟨(vV T.V (io (β π))).toNat, by omega, fun a => ?_⟩
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    obtain ⟨u, hu⟩ := exists_unit_mul_zpow hinj hr hp ha
    have h1 : valV T.V (io (β u)) = 1 := by
      rw [hc']
      refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.mp fun h => ?_)
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h (u.isUnit.map b)
    rw [Int.toNat_of_nonneg hpos.le]
    generalize vLa la a = n at hu
    rw [hu]
    simp only [vV, map_mul, map_zpow₀, h1, one_mul, WithZero.log_zpow]
    simp [mul_comm]

end GlobalTheory.PlaceLocalRing
