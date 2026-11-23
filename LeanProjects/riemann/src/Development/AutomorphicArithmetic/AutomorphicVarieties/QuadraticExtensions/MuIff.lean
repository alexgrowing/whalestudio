import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.muIff :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] (n : ℕ) [NeZero n], (∃ ζ : L, IsPrimitiveRoot ζ n) ↔ galOf ℚ L Ω ≤ (galChar Ω n).ker := by
  intro Ω _ _ _ L _ _ _ n _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  have key : ∀ g : G ℚ Ω, ∀ z : Ω, IsPrimitiveRoot z n → (g z = z ↔ galChar Ω n g = 1) := by
    intro g z hz
    rw [galChar_spec n g z hz.pow_eq_one]
    have hiff : z ^ ((galChar Ω n g : ZMod n).val) = z ↔
        (((galChar Ω n g : ZMod n).val : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne n)
      have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp hz
      nth_rewrite 2 [← pow_one (u : Ω)]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
        pow_eq_pow_iff_modEq, ← hu.eq_orderOf, ZMod.natCast_eq_natCast_iff]
    rw [hiff, ZMod.natCast_zmod_val, Nat.cast_one, ← Units.val_one, Units.val_inj]
  constructor
  · rintro ⟨ζ, hζ⟩ g hg
    rw [MonoidHom.mem_ker, ← key g _ (hζ.map_of_injective (algebraMap L Ω).injective)]
    exact hg ζ
  · intro hle
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
    haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    obtain ⟨ζ, hζ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) z).mpr (fun f => by
      have hf := hle (galEmb_mem ℚ L Ω f)
      rw [MonoidHom.mem_ker, ← key _ z hz, galEmb_apply] at hf
      exact hf)
    refine ⟨ζ, ?_⟩
    rw [← hζ] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective (algebraMap L Ω).injective).mp hz
