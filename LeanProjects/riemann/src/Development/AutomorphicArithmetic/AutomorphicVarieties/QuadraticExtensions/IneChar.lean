import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hv := congrArg A.valuation h
  rw [map_pow, map_one] at hv
  exact (pow_eq_one_iff.mp hv).resolve_right hm

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff]
    refine Subring.sum_mem A.toSubring (fun j _ => ?_)
    have hj : η ^ j ∈ A := by
      rw [← ValuationSubring.valuation_le_one_iff, map_pow, h1, one_pow]
    exact hj
  rw [← mul_neg_geom_sum, map_mul, Valuation.map_sub_swap]
  exact mul_lt_one_of_lt_of_le h hS

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  have hS : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have hg := mul_neg_geom_sum η m
    rw [hη, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have h1 : A.valuation η = 1 := aux_one A hm hη
  have hlt : A.valuation ((m : Ω) - ∑ i ∈ Finset.range m, η ^ i) < 1 := by
    have he : (m : Ω) - ∑ i ∈ Finset.range m, η ^ i = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [he]
    exact Valuation.map_sum_lt _ one_ne_zero (fun i _ => power_bounds_of_between A h1 h i)
  rw [hS, sub_zero] at hlt
  exact hv hlt

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hI : g ∈ Inertia (F := ℚ) A := hg
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have hv1 := aux_one A hm hζ
  have key := hI.2 ζ hv1.le
  have hη : (g ζ * ζ⁻¹) ^ m = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : A.valuation (g ζ * ζ⁻¹ - 1) < 1 := by
    have he : g ζ * ζ⁻¹ - 1 = (g ζ - ζ) * ζ⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, map_mul, map_inv₀, hv1, inv_one, mul_one]
    exact key
  have hfin := root_of_unity_eq_one_of_close_residue A hm hA hη hlt
  rwa [mul_inv_eq_one₀ hζ0] at hfin

theorem UpperTheory.V.Two.ineChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] (A : ValuationSubring Ω), ¬ A.valuation (m : Ω) < 1 → Ine (F := ℚ) A ≤ (galChar Ω m).ker := by
  intro Ω _ _ _ m _ A hA g hg
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hfix := inertia_fixes_prime_to_roots A (NeZero.ne m) hA hg hz.pow_eq_one
  rw [galChar_spec m g z hz.pow_eq_one] at hfix
  obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne m)
  have hu : IsPrimitiveRoot u m := IsPrimitiveRoot.coe_units_iff.mp hz
  have heq : u ^ ((galChar Ω m g : ZMod m).val) = u ^ 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_one]
    exact hfix
  have hmod := pow_eq_pow_iff_modEq.mp heq
  rw [← hu.eq_orderOf] at hmod
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((galChar Ω m g : ZMod m)), ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
