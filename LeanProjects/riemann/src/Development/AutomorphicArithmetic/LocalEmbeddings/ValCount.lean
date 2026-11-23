import Mathlib

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace GlobalTheory.ValCount

variable {K L : Type} [Field K] [Field L]

open Classical in

def vord (V : ValuationSubring L) (x : L) : ℤ :=
  if h : IsDiscreteValuationRing V then (haveI := h; WithZero.log (Ring.ordFrac V x)) else 0

def vres (φ : K →+* L) (V : ValuationSubring L) : V.comap φ →+* V :=
  φ.restrict (V.comap φ) V fun _ hx => hx

@[simp] theorem coe_vres (φ : K →+* L) (V : ValuationSubring L) (a : V.comap φ) :
    ((vres φ V a : V) : L) = φ a := rfl

theorem mem_nonunits_comap (φ : K →+* L) (V : ValuationSubring L) (a : K) :
    a ∈ (V.comap φ).nonunits ↔ φ a ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

instance isLocalHom_vres (φ : K →+* L) (V : ValuationSubring L) : IsLocalHom (vres φ V) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hu
  have h : (a : K) ∈ (V.comap φ).nonunits := (ValuationSubring.coe_mem_nonunits_iff).2 hu
  rw [mem_nonunits_comap] at h
  exact (V.coe_mem_nonunits_iff (a := vres φ V a)).1 h ha

def vdeg (φ : K →+* L) (V : ValuationSubring L) : ℕ :=
  letI := (ResidueField.map (vres φ V)).toAlgebra
  Module.finrank (ResidueField (V.comap φ)) (ResidueField V)

def rnorm (φ : K →+* L) : L →* K :=
  letI := φ.toAlgebra
  Algebra.norm K

theorem vord_eq (V : ValuationSubring L) [h : IsDiscreteValuationRing V] (x : L) :
    vord V x = WithZero.log (Ring.ordFrac V x) := dif_pos h

theorem vord_mul (V : ValuationSubring L) {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    vord V (x * y) = vord V x + vord V y := by
  by_cases h : IsDiscreteValuationRing V
  · rw [vord_eq, vord_eq, vord_eq, map_mul,
      WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  · simp [vord, h]

theorem vord_one (V : ValuationSubring L) : vord V 1 = 0 := by
  have := vord_mul V (one_ne_zero (α := L)) one_ne_zero
  rw [mul_one] at this
  omega

theorem vord_zpow (V : ValuationSubring L) (x : L) (n : ℤ) : vord V (x ^ n) = n * vord V x := by
  by_cases h : IsDiscreteValuationRing V
  · rw [vord_eq, vord_eq, map_zpow₀, WithZero.log_zpow, zsmul_eq_mul, Int.cast_id]
  · simp [vord, h]

theorem vord_pow (V : ValuationSubring L) (x : L) (n : ℕ) : vord V (x ^ n) = n * vord V x := by
  rw [← zpow_natCast, vord_zpow]

theorem vord_prod (V : ValuationSubring L) {ι : Type} (s : Finset ι) (x : ι → L) (hx : ∀ i ∈ s, x i ≠ 0) :
    vord V (∏ i ∈ s, x i) = ∑ i ∈ s, vord V (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vord_one V
  | insert a s ha ih =>
    have h : ∀ i ∈ s, x i ≠ 0 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vord_mul V (hx a (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.2 h), ih h]

theorem vord_of_isUnit (V : ValuationSubring L) {a : V} (ha : IsUnit a) : vord V (a : L) = 0 := by
  by_cases h : IsDiscreteValuationRing V
  · rw [vord_eq]
    exact (congrArg WithZero.log (Ring.ordFrac_of_isUnit (K := L) ha)).trans WithZero.log_one
  · simp [vord, h]

theorem vord_eq_zero_of_mem (V : ValuationSubring L) {x : L} (h0 : x ≠ 0) (hx : x ∈ V) (hx' : x⁻¹ ∈ V) :
    vord V x = 0 :=
  vord_of_isUnit V (a := ⟨x, hx⟩) (isUnit_iff_exists_inv.2 ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩)

theorem vord_irreducible (V : ValuationSubring L) [IsDiscreteValuationRing V] {a : V} (ha : Irreducible a) :
    vord V (a : L) = 1 := by
  rw [vord_eq]
  exact (congrArg WithZero.log (Ring.ordFrac_irreducible (K := L) ha)).trans (WithZero.log_exp _)

theorem vord_coe (V : ValuationSubring L) [IsDiscreteValuationRing V] {a : V} (ha : a ≠ 0) :
    vord V (a : L) = (IsDiscreteValuationRing.addVal V a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : ((u : V) : L) ≠ 0 := by simpa using u.ne_zero
  have h2 : (ϖ : L) ≠ 0 := by simpa using hϖ.ne_zero
  rw [IsDiscreteValuationRing.addVal_def' u hϖ k]
  push_cast
  rw [vord_mul V h1 (pow_ne_zero _ h2), vord_of_isUnit V u.isUnit, vord_pow, vord_irreducible V hϖ]
  simp

theorem vord_pos (V : ValuationSubring L) [IsDiscreteValuationRing V] {x : L} (h0 : x ≠ 0) (hx : x ∈ V.nonunits) :
    0 < vord V x := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : V, a ∈ maximalIdeal V ∧ (a : L) = x := by
    have h := V.nonunits_subset hx
    exact ⟨⟨x, h⟩, V.coe_mem_nonunits_iff.1 hx, rfl⟩
  have ha0 : a ≠ 0 := by simpa using h0
  rw [vord_coe V ha0]
  have h1 := mt IsDiscreteValuationRing.addVal_eq_zero_iff.1 ha
  have h2 := mt IsDiscreteValuationRing.addVal_eq_top_iff.1 ha0
  exact_mod_cast Nat.pos_of_ne_zero (by simp [ENat.toNat_eq_zero, h1, h2])

theorem exists_eq_unit_mul_zpow (W : ValuationSubring K) [IsDiscreteValuationRing W] {ϖ : W} (hϖ : Irreducible ϖ)
    {a : K} (ha : a ≠ 0) : ∃ (n : ℤ) (u : W), IsUnit u ∧ a = (u : K) * (ϖ : K) ^ n := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨n, u, u.isUnit, ?_⟩
  rw [hu, Units.smul_def, Algebra.smul_def]; rfl

theorem exists_vord_map (φ : K →+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V]
    [IsDiscreteValuationRing (V.comap φ)] :
    ∃ e : ℤ, 0 < e ∧ ∀ a : K, a ≠ 0 → vord V (φ a) = e * vord (V.comap φ) a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (V.comap φ)
  have h2 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have h2' : φ ϖ ≠ 0 := (map_ne_zero φ).2 h2
  have h4 : (ϖ : K) ∈ (V.comap φ).nonunits := (ValuationSubring.coe_mem_nonunits_iff (a := ϖ)).2 hϖ.not_isUnit
  refine ⟨vord V (φ ϖ), vord_pos V h2' ((mem_nonunits_comap φ V _).1 h4), fun a ha => ?_⟩
  obtain ⟨n, u, hu, hu'⟩ := exists_eq_unit_mul_zpow (V.comap φ) hϖ ha
  have h1 : (u : K) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
  have h3 : vord V (φ u) = 0 := by
    have := vord_of_isUnit V (a := vres φ V u) (hu.map (vres φ V))
    rwa [coe_vres] at this
  have h5 : vord V (φ a) = n * vord V (φ ϖ) := by
    rw [hu', map_mul, map_zpow₀, vord_mul V ((map_ne_zero φ).2 h1) (zpow_ne_zero _ h2'), h3, vord_zpow, zero_add]
  have h6 : vord (V.comap φ) a = n := by
    rw [hu', vord_mul _ h1 (zpow_ne_zero _ h2), vord_of_isUnit _ hu, vord_zpow, vord_irreducible _ hϖ]
    ring
  rw [h5, h6, mul_comm]

end GlobalTheory.ValCount

end
