import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LayerLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ExistsNumberFieldIsAbFieldFinrankEqDeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.layerex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) (m : ℕ) [NeZero m] (h : ψ.conductor ∣ m) :
    (Chr.cls ℚ Ω m).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  obtain ⟨hd, χ₀, hχ⟩ := ψ.factorsThrough_conductor
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have e1 := (Chr.clsFacts ℚ Ω N).2.1 ψ.conductor hd
  have e2 := (Chr.clsFacts ℚ Ω m).2.1 ψ.conductor h
  have hc : Chr.cls ℚ Ω ψ.conductor σ = 1 := by
    rw [← e2, MonoidHom.comp_apply, hσ, map_one]
  have hu : ∀ u : (ZMod N)ˣ, MulChar.toUnitHom ψ u = MulChar.toUnitHom χ₀ (ZMod.unitsMap hd u) := by
    intro u
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom]
    conv_lhs => rw [hχ]
    rw [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  unfold Chr.dirG
  rw [MonoidHom.comp_apply, hu, ← MonoidHom.comp_apply (ZMod.unitsMap hd), e1, hc, map_one]

theorem UpperTheory.V.HV.ivField :
    ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω],
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁) (_ : Algebra L₁ Ω)
        (_ : IsAlgClosure L₁ Ω) (_ : IsAbelianGalois ℚ L₁), IsAbField (Lchi χ l) L₀ ∧ IsLayer l j L₀ L₁ ∧ Module.finrank ℚ L₁ ≤ l * χ.N * l ^ j ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.conductor ∣ χ.N → galOf ℚ L₁ Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro χ l _ j hl2 Ω _ _ _
  haveI := χ.ne
  have hlp : l.Prime := Fact.out
  have hAm : (Lchi χ l).m = l * χ.N := by
    simp only [Lchi, AbF.cyc]
    exact max_eq_left (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hlp.ne_zero (NeZero.ne _)))
  have hldvd : l ∣ (Lchi χ l).m := by rw [hAm]; exact dvd_mul_right l _
  obtain ⟨L₀, i0, i1, hab, hdeg⟩ := exists_numberField_isAbField_finrank_eq_deg (Lchi χ l)
  have hmu : (Lchi χ l).HasMu l := by
    refine ⟨hldvd, ?_⟩
    rintro a ⟨u, hu, hua⟩
    have hu1 : u = 1 := (Subgroup.mem_bot).mp hu
    rw [hu1, Units.val_one] at hua
    have h2 : ((a : ℕ) : ZMod (Lchi χ l).m) = ((1 : ℕ) : ZMod (Lchi χ l).m) := by
      rw [Nat.cast_one]; exact hua.symm
    exact Nat.ModEq.of_dvd hldvd ((ZMod.natCast_eq_natCast_iff _ _ _).mp h2)
  obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot (Lchi χ l) l hlp hl2 L₀ hab).mp hmu
  obtain ⟨L₁, i2, i3, i4, hlay⟩ := exists_cyclotomic_layer_of_primitiveRoot l j hlp hl2 L₀ ⟨z, hz⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra L₁ Ω := (IsAlgClosed.lift (R := ℚ) (S := L₁) (M := Ω)).toRingHom.toAlgebra
  letI : Algebra L₀ Ω := ((algebraMap L₁ Ω).comp (algebraMap L₀ L₁)).toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ℚ L₁ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L₀ L₁ := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI hcl : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) L₁⟩
  obtain ⟨N', hN', H, hlev⟩ := Chr.layerLevel (Lchi χ l) l j hlp L₀ L₁ hab hlay
  obtain ⟨habel, -, -⟩ := Chr.levGal L₁ N' H hlev
  have hlev0 := Chr.abLevel.1 (Lchi χ l) L₀ hab
  have hgal0 := ((Chr.levGal L₀ _ _ hlev0).2.2 Ω).1
  refine ⟨L₀, i0, i1, L₁, i2, i3, i4, inferInstance, hcl, habel, hab, hlay, ?_, ?_⟩
  · rw [← Module.finrank_mul_finrank ℚ L₀ L₁, hdeg, hlay.2]
    apply Nat.mul_le_mul_right
    rw [AbF.deg]
    show (⊥ : Subgroup (ZMod (Lchi χ l).m)ˣ).index ≤ l * χ.N
    rw [Subgroup.index_bot, ← hAm]
    haveI : NeZero (Lchi χ l).m := ⟨(AbF.pos _).ne'⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  · intro O _ _ N _ ψ hψ
    calc galOf ℚ L₁ Ω ≤ galOf ℚ L₀ Ω := galOf_le ℚ L₀ Ω L₁
      _ = Chr.levH ℚ Ω (Lchi χ l).H := hgal0
      _ ≤ (Chr.dirG ℚ Ω ψ).ker := by
        rw [Chr.levH]
        show Subgroup.comap _ ⊥ ≤ _
        rw [MonoidHom.comap_bot]
        exact ker_le Ω ψ _ (hψ.trans (hAm ▸ dvd_mul_left _ _))
