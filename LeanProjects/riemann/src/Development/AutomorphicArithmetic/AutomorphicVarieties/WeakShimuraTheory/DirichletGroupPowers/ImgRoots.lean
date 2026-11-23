import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.large₂.imgRoots :
    ∀ {O : Type} [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (x : Oˣ), x ^ orderOf χ = 1 → ∃ b : (ZMod N)ˣ, χ.toUnitHom b = x := by
  intro O _ _ N _ χ x hx
  have hn : 0 < orderOf χ := orderOf_pos χ
  haveI : NeZero (orderOf χ) := ⟨hn.ne'⟩
  haveI : Finite χ.toUnitHom.range :=
    Finite.of_surjective χ.toUnitHom.rangeRestrict χ.toUnitHom.rangeRestrict_surjective
  have hle : χ.toUnitHom.range ≤ rootsOfUnity (orderOf χ) O := by
    rintro _ ⟨b, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' χ hn.ne', pow_orderOf_eq_one,
      MulChar.one_apply_coe, Units.val_one]
  have hcard : orderOf χ ≤ Nat.card χ.toUnitHom.range := by
    have hpos : 0 < Nat.card χ.toUnitHom.range := Nat.card_pos
    apply orderOf_le_of_pow_eq_one hpos
    refine MulChar.ext fun a => ?_
    rw [MulChar.pow_apply' χ hpos.ne', MulChar.one_apply_coe]
    have h1 := pow_card_eq_one' (G := χ.toUnitHom.range) (x := ⟨χ.toUnitHom a, a, rfl⟩)
    have h2 := congrArg (fun u : χ.toUnitHom.range => ((u : Oˣ) : O)) h1
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h2
    rw [← MulChar.coe_toUnitHom]
    exact h2
  have heq : χ.toUnitHom.range = rootsOfUnity (orderOf χ) O :=
    Subgroup.eq_of_le_of_card_ge hle ((card_rootsOfUnity O (orderOf χ)).trans hcard)
  have hxmem : x ∈ rootsOfUnity (orderOf χ) O := (mem_rootsOfUnity _ _).2 hx
  rw [← heq] at hxmem
  obtain ⟨b, hb⟩ := hxmem
  exact ⟨b, hb⟩
