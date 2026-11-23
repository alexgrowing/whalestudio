import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

open UpperTheory.V in
private theorem quartic_character_eq_one (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 4)
    (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (h : σ ζ = ζ) : eta4 Ω σ = 1 := by
  unfold eta4 Chr.dirG
  rw [MonoidHom.comp_apply]
  have hc := Chr.cls_spec (k := ℚ) (Ω := Ω) 4 σ ζ hζ.pow_eq_one
  rw [h] at hc
  have hv : ((Chr.cls ℚ Ω 4 σ : (ZMod 4)ˣ) : ZMod 4).val = 1 := by
    have h1 : ζ ^ 1 = ζ ^ ((Chr.cls ℚ Ω 4 σ : (ZMod 4)ˣ) : ZMod 4).val := by rwa [pow_one]
    have hlt := ZMod.val_lt ((Chr.cls ℚ Ω 4 σ : (ZMod 4)ˣ) : ZMod 4)
    exact (hζ.pow_inj (by norm_num) hlt h1).symm
  have hu : Chr.cls ℚ Ω 4 σ = 1 := Units.ext (ZMod.val_injective 4 (by rw [hv]; rfl))
  rw [hu, map_one]

theorem UpperTheory.exists_absGalois_fixing_sqrt_neg_one_cyclotomic_ne_one :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ σ : Formalism.ConjugateSelfDual.G ℚ Ω, eta4 Ω σ = 1 ∧ cycMod ℚ Ω l 1 σ ≠ 1 := by
  intro Ω _ _ _ l _ hl2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  obtain ⟨m, hm⟩ : ∃ m, l = 2 * m + 1 := hlp.eq_two_or_odd'.resolve_left hl2
  have hm1 : 1 ≤ m := by have := hlp.two_le; omega
  haveI : NeZero (4 * l) := ⟨by omega⟩
  let a : ZMod (4 * l) := ((4 * m + 1 : ℕ) : ZMod (4 * l))
  have ha : a * a = 1 := by
    have hnat : ((4 * m + 1) * (4 * m + 1) : ℕ) = 1 + (4 * l) * (2 * m) := by rw [hm]; ring
    show ((4 * m + 1 : ℕ) : ZMod (4 * l)) * ((4 * m + 1 : ℕ) : ZMod (4 * l)) = 1
    rw [← Nat.cast_mul, hnat, Nat.cast_add, Nat.cast_one, Nat.cast_mul (4 * l), ZMod.natCast_self,
      zero_mul, add_zero]
  let u : (ZMod (4 * l))ˣ := ⟨a, a, ha, ha⟩
  obtain ⟨σ, hσ⟩ := (UpperTheory.V.Chr.clsOnto Ω (4 * l)).1 u
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (4 * l)
  have hval : ((u : ZMod (4 * l))).val = 4 * m + 1 := by
    show (((4 * m + 1 : ℕ) : ZMod (4 * l))).val = 4 * m + 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hspec : ∀ t : Ω, t ^ (4 * l) = 1 → σ t = t ^ (4 * m + 1) := by
    intro t ht
    rw [UpperTheory.V.Chr.cls_spec (4 * l) σ t ht, hσ, hval]
  refine ⟨σ, ?_, ?_⟩
  · have h4l : (ζ ^ l) ^ (4 * l) = 1 := by
      rw [← pow_mul, mul_comm l (4 * l), pow_mul, hζ.pow_eq_one, one_pow]
    have h4 : (ζ ^ l) ^ 4 = 1 := by rw [← pow_mul, mul_comm, hζ.pow_eq_one]
    refine quartic_character_eq_one Ω (ζ ^ l) (hζ.pow (by omega) (mul_comm 4 l)) σ ?_
    rw [hspec _ h4l, pow_succ, pow_mul, h4, one_pow, one_mul]
  · intro hcyc
    have hprim : IsPrimitiveRoot (ζ ^ 4) l := hζ.pow (by omega) rfl
    have h4l : (ζ ^ 4) ^ (4 * l) = 1 := by
      rw [← pow_mul, mul_comm 4 (4 * l), pow_mul, hζ.pow_eq_one, one_pow]
    haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
    unfold cycMod cycZ at hcyc
    have hz : PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l
        (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
      simpa using congrArg Units.val hcyc
    have hs := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ)
      (ζ ^ 4) (by rw [pow_one]; exact hprim.pow_eq_one)
    rw [hz, ZMod.val_one'' (by rw [pow_one]; exact hlp.one_lt.ne')] at hs
    have hs' : σ (ζ ^ 4) = (ζ ^ 4) ^ 1 := hs
    have heq := (hspec _ h4l).symm.trans hs'
    have hred : (ζ ^ 4) ^ (4 * m + 1) = (ζ ^ 4) ^ (2 * m) := by
      rw [show 4 * m + 1 = 2 * m + l by omega, pow_add, hprim.pow_eq_one, mul_one]
    rw [hred] at heq
    have := hprim.pow_inj (by omega) (by omega) heq
    omega
