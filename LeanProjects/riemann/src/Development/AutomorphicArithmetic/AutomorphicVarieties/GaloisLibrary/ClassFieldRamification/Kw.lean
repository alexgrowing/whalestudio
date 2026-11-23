import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsPrimeMemOfMem

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kw :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (L : IntermediateField ℚ Ω) [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L], ∃ (N : ℕ) (ζ : Ω), 0 < N ∧ IsPrimitiveRoot ζ N ∧ L ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ L hfd hab
  obtain ⟨m, hm⟩ := @GroundTheory.Global.exists_le_rayClassField ℚ _ _ Ω _ _ _ L hfd hab
  have hn : Ideal.absNorm m.ideal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact m.ideal_ne_bot
  haveI : NeZero ((Ideal.absNorm m.ideal : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (Ideal.absNorm m.ideal)
  exact ⟨_, ζ, Nat.pos_of_ne_zero hn, hζ, hm.trans (kwRay Ω m ζ hζ)⟩
