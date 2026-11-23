import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ExistsNumberFieldIsAbFieldFinrankEqDeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem idx_le (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) :
    ψ.toUnitHom.ker.index ≤ orderOf ψ := by
  have hpos := MulChar.orderOf_pos ψ
  haveI : NeZero (orderOf ψ) := ⟨hpos.ne'⟩
  rw [Subgroup.index_ker]
  calc Nat.card ψ.toUnitHom.range ≤ Nat.card (rootsOfUnity (orderOf ψ) O) := by
        apply Subgroup.card_le_of_le
        rintro _ ⟨u, rfl⟩
        rw [mem_rootsOfUnity]
        ext
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' ψ hpos.ne',
          pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
    _ ≤ orderOf ψ := card_rootsOfUnity O _

theorem UpperTheory.V.HV.vsField :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Ω) (_ : IsAlgClosure L Ω) (_ : IsAbelianGalois ℚ L), HasMuQ l L ∧
        Module.finrank ℚ L ≤ orderOf ψ * l ∧ Nonempty (L →ₐ[ℚ] CyclotomicField (l * N) ℚ) ∧ galOf ℚ L Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro Ω _ _ _ l hl hl2 O _ _ N _ ψ
  have hlp : l.Prime := hl.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  haveI hMz : NeZero (l * N) := ⟨mul_ne_zero hlp.ne_zero (NeZero.ne N)⟩
  let φN : (ZMod (l * N))ˣ →* (ZMod N)ˣ := ZMod.unitsMap (dvd_mul_left N l)
  let φl : (ZMod (l * N))ˣ →* (ZMod l)ˣ := ZMod.unitsMap (dvd_mul_right l N)
  let H : Subgroup (ZMod (l * N))ˣ := (ψ.toUnitHom.comp φN).ker ⊓ φl.ker
  let A : AbF := ⟨l * N, Nat.pos_of_ne_zero (NeZero.ne (l * N)), H⟩
  obtain ⟨L, fL, nfL, hab, -⟩ := exists_numberField_isAbField_finrank_eq_deg A
  have hlev : Chr.HasLevel L (l * N) H := Chr.abLevel.1 A L hab
  obtain ⟨hgal, hfin, hΩ⟩ := Chr.levGal L (l * N) H hlev
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let f : L →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI : Algebra L Ω := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L Ω := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI hcl : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  refine ⟨L, fL, nfL, inferInstance, hcl, hgal, ?_, ?_, ?_, ?_⟩
  · have hmu : A.HasMu l := by
      unfold AbF.HasMu
      refine ⟨dvd_mul_right l N, ?_⟩
      intro a ha
      unfold AbF.ker at ha
      obtain ⟨u, hu, hua⟩ := ha
      have h1 : φl u = 1 := MonoidHom.mem_ker.mp hu.2
      have h2 : ((φl u : (ZMod l)ˣ) : ZMod l) = (a : ZMod l) := by
        simp only [φl, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply]
        rw [hua, ZMod.cast_natCast (dvd_mul_right l N)]
      rw [h1, Units.val_one] at h2
      exact (ZMod.natCast_eq_natCast_iff a 1 l).mp (by rw [← h2, Nat.cast_one])
    obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot A l hlp hl2 L hab).mp hmu
    unfold HasMuQ
    rw [if_neg hl2]
    exact ⟨z, hz⟩
  · rw [hfin]
    refine (Subgroup.index_inf_le).trans (Nat.mul_le_mul ?_ ?_)
    · rw [← MonoidHom.comap_ker, Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)]
      exact idx_le O N ψ
    · rw [Subgroup.index_ker]
      refine (Subgroup.card_le_card_group _).trans ?_
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact Nat.totient_le l
  · have hab' := hab
    unfold IsAbField at hab'
    obtain ⟨N', hN', j, ζ, hmN, hζ, h3⟩ := hab'
    haveI : NeZero N' := hN'
    haveI : NeZero ((N' : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N')⟩
    haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension N' ℚ
    haveI : IsGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isGalois {N'} ℚ _
    haveI : FiniteDimensional ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.finiteDimensional {N'} ℚ _
    haveI : NeZero ((l * N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne (l * N))⟩
    haveI : IsCyclotomicExtension {l * N} ℚ (CyclotomicField (l * N) ℚ) :=
      CyclotomicField.isCyclotomicExtension (l * N) ℚ
    have hmN' : l * N ∣ N' := hmN
    have hdpos : N' / (l * N) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N')) hmN')
        (Nat.pos_of_ne_zero (NeZero.ne (l * N)))).ne'
    have hη : IsPrimitiveRoot (ζ ^ (N' / (l * N))) (l * N) := by
      have := hζ.pow_of_dvd hdpos (Nat.div_dvd_of_dvd hmN')
      rwa [Nat.div_div_self hmN' (NeZero.ne N')] at this
    let F : IntermediateField ℚ (CyclotomicField N' ℚ) := IntermediateField.adjoin ℚ {ζ ^ (N' / (l * N))}
    haveI : IsCyclotomicExtension {l * N} ℚ F := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hmem : ∀ x, j x ∈ F := by
      intro x
      rw [← IsGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hτη : τ (ζ ^ (N' / (l * N))) = ζ ^ (N' / (l * N)) :=
        (IntermediateField.mem_fixingSubgroup_iff F τ).mp hτ _
          (IntermediateField.mem_adjoin_simple_self ℚ _)
      have hτζ : τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N')).val := (hζ.autToPow_spec ℚ τ).symm
      have hpow : (ζ ^ (N' / (l * N))) ^ ((hζ.autToPow ℚ τ : ZMod N')).val = ζ ^ (N' / (l * N)) := by
        calc (ζ ^ (N' / (l * N))) ^ ((hζ.autToPow ℚ τ : ZMod N')).val
            = (ζ ^ ((hζ.autToPow ℚ τ : ZMod N')).val) ^ (N' / (l * N)) := by
              rw [← pow_mul, ← pow_mul, mul_comm]
          _ = (τ ζ) ^ (N' / (l * N)) := by rw [hτζ]
          _ = τ (ζ ^ (N' / (l * N))) := (map_pow τ ζ _).symm
          _ = ζ ^ (N' / (l * N)) := hτη
      have hne : ζ ^ (N' / (l * N)) ≠ 0 := hη.ne_zero (NeZero.ne (l * N))
      have hz : (ζ ^ (N' / (l * N))) ^ ((((hζ.autToPow ℚ τ : ZMod N')).val : ℤ) - 1) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_one, hpow, div_self hne]
      have hd := (hη.zpow_eq_one_iff_dvd _).mp hz
      have hc : ((((((hζ.autToPow ℚ τ : ZMod N')).val : ℤ) - 1 : ℤ)) : ZMod (l * N)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l * N)).mpr hd
      push_cast at hc
      have hker : A.ker ((hζ.autToPow ℚ τ : ZMod N')).val := by
        unfold AbF.ker
        exact ⟨1, Subgroup.one_mem _, by rw [Units.val_one]; exact (sub_eq_zero.mp hc).symm⟩
      exact ((h3 τ _ hτζ).mpr hker) x
    exact ⟨(IsCyclotomicExtension.algEquiv {l * N} ℚ F (CyclotomicField (l * N) ℚ)).toAlgHom.comp
      (j.codRestrict F.toSubalgebra hmem)⟩
  · intro σ hσ
    rw [(hΩ Ω).1] at hσ
    unfold Chr.levH at hσ
    rw [Subgroup.mem_comap] at hσ
    rw [MonoidHom.mem_ker]
    unfold Chr.dirG
    rw [← (Chr.clsFacts ℚ Ω (l * N)).2.1 N (dvd_mul_left N l)]
    exact MonoidHom.mem_ker.mp hσ.1
