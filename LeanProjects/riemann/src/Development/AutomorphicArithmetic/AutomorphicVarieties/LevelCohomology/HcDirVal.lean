import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.dirVal :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (g : G ℚ Ω), ∃ a : ℤ, IsCoprime a M ∧ ∀ (N : ℕ) [NeZero N], N ∣ M → ∀ (O : Type) [CommRing O] (χ : DirichletCharacter O N), (Chr.dirG ℚ Ω χ g : O) = χ a := by
  intro Ω _ _ _ M _ g
  refine ⟨(((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ), ?_, fun N _ h O _ χ => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime _)
  · have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω M).2.1 N h) g
    have h2 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = ((((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod N) := by
      rw [← h1, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]
    rw [Int.cast_natCast, ← h2]
    exact MulChar.coe_toUnitHom χ _
