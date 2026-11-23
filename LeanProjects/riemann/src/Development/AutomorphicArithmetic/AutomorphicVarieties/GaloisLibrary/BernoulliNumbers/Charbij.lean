import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_charbij :
    ∀ {N : ℕ} [NeZero N] {K Ω : Type} [Field K] [Field Ω] [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)] (f : K →+* Ω) (P : Set (Subgroup (ZMod N)ˣ)), Set.BijOn (fun χ : DirichletCharacter K N => (χ.ringHomComp f : DirichletCharacter Ω N)) (charSet K P) (charSet Ω P) := by
  intro N _ K Ω _ _ _ f P
  have hf : Function.Injective f := f.injective
  have hker : ∀ χ : DirichletCharacter K N, (MulChar.toUnitHom (χ.ringHomComp f)).ker = (MulChar.toUnitHom χ).ker := by
    intro χ
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simp only [charSet, Set.mem_setOf_eq] at hχ ⊢
    rw [hker]
    exact hχ
  · intro χ₁ _ χ₂ _ h
    ext u
    have h' := congrArg (fun ψ : DirichletCharacter Ω N => ψ u) h
    simp only [MulChar.ringHomComp_apply] at h'
    exact hf h'
  · intro χ' hχ'
    have he : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent (ZMod N)ˣ)
    have hne : (primitiveRoots (Monoid.exponent (ZMod N)ˣ) K).Nonempty :=
      ⟨ζ, (mem_primitiveRoots (NeZero.pos _)).mpr hζ⟩
    have hmem : ∀ u, MulChar.toUnitHom χ' u ∈ rootsOfUnity (Monoid.exponent (ZMod N)ˣ) Ω := by
      intro u
      rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    let ψ : (ZMod N)ˣ →* Kˣ := (rootsOfUnity (Monoid.exponent (ZMod N)ˣ) K).subtype.comp
      ((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm.toMonoidHom.comp
        ((MulChar.toUnitHom χ').codRestrict _ hmem))
    have hcomp : (MulChar.ofUnitHom ψ).ringHomComp f = χ' := by
      ext u
      rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe]
      show f (((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm ⟨MulChar.toUnitHom χ' u, hmem u⟩ : Kˣ) : K) = χ' u
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp [MulChar.coe_toUnitHom]
    refine ⟨MulChar.ofUnitHom ψ, ?_, hcomp⟩
    simp only [charSet, Set.mem_setOf_eq] at hχ' ⊢
    rw [← hker, hcomp]
    exact hχ'
