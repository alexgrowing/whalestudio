import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

section NormDiscrete

variable {Ω : Type*} [Field Ω] {v : AddValuation Ω (WithTop ℤ)}

theorem normDiscrete_mem_vRing_iff (x : Ω) : x ∈ vRing v ↔ 0 ≤ v x := Iff.rfl

theorem normDiscrete_map_inv {x : Ω} {n : ℤ} (hx : v x = (n : WithTop ℤ)) :
    v x⁻¹ = ((-n : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_inv, hx]
  rfl

theorem normDiscrete_isUnit_iff (x : vRing v) : IsUnit x ↔ v (x : Ω) = 0 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have h1 : v (x : Ω) + v (y : Ω) = 0 := by
      rw [← AddValuation.map_mul, ← MulMemClass.coe_mul, hy, OneMemClass.coe_one,
        AddValuation.map_one]
    exact ValPl.wt_add_eq_zero x.2 y.2 h1
  · intro h
    have hx0 : (x : Ω) ≠ 0 := by
      intro h0
      rw [h0, AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h
    have h1 : v (x : Ω)⁻¹ = 0 := by
      have := normDiscrete_map_inv (v := v) (n := 0) h
      simpa using this
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(x : Ω)⁻¹, (normDiscrete_mem_vRing_iff _).mpr h1.ge⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem normDiscrete_associated_pow {π : vRing v} (hπ : v (π : Ω) = 1) (x : vRing v) {n : ℕ}
    (hx : v (x : Ω) = ((n : ℤ) : WithTop ℤ)) : Associated (π ^ n) x := by
  have hπ0 : (π : Ω) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hπ
    exact WithTop.top_ne_one hπ
  have hpn : v ((π : Ω) ^ n) = ((n : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_pow, hπ]
    simp
  have h1 : v ((x : Ω) * ((π : Ω) ^ n)⁻¹) = 0 := by
    rw [AddValuation.map_mul, normDiscrete_map_inv hpn, hx, ← WithTop.coe_add]
    simp
  let u : vRing v := ⟨_, (normDiscrete_mem_vRing_iff _).mpr h1.ge⟩
  have hu : IsUnit u := (normDiscrete_isUnit_iff u).mpr h1
  refine ⟨hu.unit, Subtype.ext ?_⟩
  have := pow_ne_zero n hπ0
  simp only [IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow, u]
  field_simp

theorem normDiscrete_exists_nat (hv : IsNormDiscrete v) (x : vRing v) (hx : x ≠ 0) :
    ∃ n : ℕ, v (x : Ω) = ((n : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hv.1 x fun h => hx (Subtype.ext h))
  have h0 : 0 ≤ v (x : Ω) := x.2
  rw [← hm] at h0 ⊢
  have h1 : 0 ≤ m := by exact_mod_cast h0
  exact ⟨m.toNat, by rw [Int.toNat_of_nonneg h1]⟩

theorem normDiscrete_irreducible {π : vRing v} (hπ : v (π : Ω) = 1) : Irreducible π := by
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · rw [normDiscrete_isUnit_iff, hπ] at h
    exact absurd h (by decide)
  · rw [normDiscrete_isUnit_iff, normDiscrete_isUnit_iff]
    have h1 : v (a : Ω) + v (b : Ω) = 1 := by
      rw [← AddValuation.map_mul, ← MulMemClass.coe_mul, ← hab, hπ]
    have ha : 0 ≤ v (a : Ω) := a.2
    have hb : 0 ≤ v (b : Ω) := b.2
    generalize v (a : Ω) = s at h1 ha ⊢
    generalize v (b : Ω) = t at h1 hb ⊢
    induction s using WithTop.recTopCoe with
    | top => simp at h1
    | coe s =>
      induction t using WithTop.recTopCoe with
      | top => simp at h1
      | coe t =>
        norm_cast at h1 ha hb ⊢
        omega

theorem normDiscrete_isDiscreteValuationRing (hv : IsNormDiscrete v) :
    IsDiscreteValuationRing (vRing v) := by
  obtain ⟨π, hπ⟩ := hv.2
  have hπm : π ∈ vRing v := by
    rw [normDiscrete_mem_vRing_iff, hπ]
    exact zero_le_one
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨π, hπm⟩, normDiscrete_irreducible hπ, fun {x} hx => ?_⟩
  obtain ⟨n, hn⟩ := normDiscrete_exists_nat hv x hx
  exact ⟨n, normDiscrete_associated_pow hπ x hn⟩

end NormDiscrete

theorem exists_complete_discreteValuationRing_of_isNormDiscrete :
    ∀ (Ω : Type) [Field Ω] (v : AddValuation Ω (WithTop ℤ)), IsNormDiscrete v →
      ∃ (V K' : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
        (_ : Field K') (_ : Algebra V K') (_ : IsFractionRing V K') (f : Ω →+* K'),
        IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
        (∀ a : Ω, (∃ x : V, algebraMap V K' x = f a) ↔ 0 ≤ v a) ∧
        (∀ (n : ℕ) (a : Ω) (x : V), algebraMap V K' x = f a →
          (IsDiscreteValuationRing.addVal V x = n ↔ v a = ((n : ℤ) : WithTop ℤ))) ∧
        ∀ x : V, ∃ (a : Ω) (x' : V), algebraMap V K' x' = f a ∧
          x - x' ∈ IsLocalRing.maximalIdeal V := by
  intro Ω _ v hv
  have hR := normDiscrete_isDiscreteValuationRing hv
  let R := vRing v
  let V := AdicCompletion (maximalIdeal R) R
  let K' := FractionRing V
  have hinj : Function.Injective ((algebraMap V K').comp (algebraMap R V)) :=
    (IsFractionRing.injective V K').comp (algebraMap_adicCompletion_injective_of_dvr R)
  let f : Ω →+* K' := IsFractionRing.lift (K := Ω) hinj
  have hf : ∀ r : R, f (r : Ω) = algebraMap V K' (algebraMap R V r) := fun r =>
    IsFractionRing.lift_algebraMap hinj r
  have hmem : ∀ a : Ω, (∃ x : V, algebraMap V K' x = f a) ↔ 0 ≤ v a := by
    intro a
    refine ⟨?_, fun h => ⟨algebraMap R V ⟨a, h⟩, (hf ⟨a, h⟩).symm⟩⟩
    rintro ⟨x, hx⟩
    by_contra hn
    have ha : a ∉ vRing v := hn
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    have hb : a⁻¹ ∈ vRing v := ((vRing v).mem_or_inv_mem a).resolve_left ha
    have h1 : algebraMap R V ⟨a⁻¹, hb⟩ * x = 1 := by
      apply IsFractionRing.injective V K'
      rw [map_mul, ← hf, hx, ← map_mul, inv_mul_cancel₀ ha0, map_one, map_one]
    have h2 : IsUnit (⟨a⁻¹, hb⟩ : R) :=
      (isUnit_map_iff (algebraMap R V) _).mp (IsUnit.of_mul_eq_one _ h1)
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h2
    have h3 : a⁻¹ * (y : Ω) = 1 := congrArg Subtype.val hy
    have h4 : (y : Ω) = a := by
      field_simp at h3
      exact h3
    exact ha (h4 ▸ y.2)
  refine ⟨V, K', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, f, inferInstance, hmem, ?_, ?_⟩
  · intro n a x hx
    have ha : a ∈ vRing v := (hmem a).mp ⟨x, hx⟩
    obtain rfl : x = algebraMap R V ⟨a, ha⟩ :=
      IsFractionRing.injective V K' (hx.trans (hf ⟨a, ha⟩))
    by_cases h0 : (⟨a, ha⟩ : R) = 0
    · have h1 : a = 0 := congrArg Subtype.val h0
      rw [h0, map_zero, IsDiscreteValuationRing.addVal_zero, h1, AddValuation.map_zero]
      exact ⟨fun h => absurd h (ENat.top_ne_coe n), fun h => absurd h WithTop.top_ne_coe⟩
    · obtain ⟨π, hπ⟩ := hv.2
      have hπm : π ∈ vRing v := by
        rw [normDiscrete_mem_vRing_iff, hπ]
        exact zero_le_one
      obtain ⟨m, hm⟩ := normDiscrete_exists_nat hv ⟨a, ha⟩ h0
      obtain ⟨u, hu⟩ := normDiscrete_associated_pow (π := ⟨π, hπm⟩) hπ ⟨a, ha⟩ hm
      have hirr := irreducible_algebraMap_adicCompletion_of_dvr
        (normDiscrete_irreducible (π := ⟨π, hπm⟩) hπ)
      have h2 : IsDiscreteValuationRing.addVal V (algebraMap R V ⟨a, ha⟩) = m :=
        IsDiscreteValuationRing.addVal_def _ (Units.map (algebraMap R V : R →* V) u) hirr m
          (by rw [← hu, map_mul, map_pow, mul_comm]; rfl)
      have hm' : v a = ((m : ℤ) : WithTop ℤ) := hm
      rw [h2, hm']
      norm_cast
  · intro x
    obtain ⟨y, hy⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue V x)
    obtain ⟨r, rfl⟩ := residue_surjective y
    refine ⟨r, algebraMap R V r, (hf r).symm, ?_⟩
    rw [ResidueField.map_residue] at hy
    rw [← residue_eq_zero_iff, map_sub, hy, sub_self]

end GlobalTheory
