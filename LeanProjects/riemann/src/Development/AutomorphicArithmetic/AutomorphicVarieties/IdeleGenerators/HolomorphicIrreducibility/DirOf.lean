import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open UpperTheory.V in
theorem UpperTheory.V.Sd.dirOf :
    UpperTheory.V.Sd.DirOf := by
  intro l _ Ω _ _ _ ι N hN φ hφ
  have : NeZero N := ⟨hN.ne'⟩
  have hs := (Chr.clsOnto Ω N).1
  have hk : (Chr.cls ℚ Ω N).ker ≤ φ.ker := fun s h => by
    have h1 : Chr.cls ℚ Ω N s = 1 := h
    refine hφ s fun ζ hζ => ?_
    rw [Chr.cls_spec N s ζ hζ, h1, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  let f := MonoidHom.liftOfRightInverse (Chr.cls ℚ Ω N) (Function.surjInv hs)
    (Function.rightInverse_surjInv hs) ⟨φ, hk⟩
  have hf : ∀ s, f (Chr.cls ℚ Ω N s) = φ s := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hk⟩ s
  let χ₀ : DirichletCharacter ℂ N := MulChar.ofUnitHom ((Units.map ι.toRingHom.toMonoidHom).comp f)
  have hd : χ₀.conductor ∣ N := χ₀.conductor_dvd_level
  have hM : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  refine ⟨χ₀.conductor, hM, χ₀.primitiveCharacter, hd, χ₀.primitiveCharacter_isPrimitive, ?_⟩
  ext s
  have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 _ hd) s
  have h2 : χ₀.primitiveCharacter (ZMod.unitsMap hd (Chr.cls ℚ Ω N s)) = χ₀ (Chr.cls ℚ Ω N s) := by
    conv_rhs => rw [← χ₀.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    simp [ZMod.unitsMap_def]
  have h3 : χ₀ (Chr.cls ℚ Ω N s) = ι (φ s) := by
    rw [← hf]
    simp [χ₀]
  rw [Chr.dirG, MonoidHom.comp_apply, ← h1, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, MonoidHom.comp_apply, h2, h3]
  simp
