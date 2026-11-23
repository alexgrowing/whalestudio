import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem hom_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k) (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) k (PadicInt.toZModPow 1 x) = f x := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (PadicInt.toZModPow 1 x)
  have h : x - n ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, map_sub, map_intCast, hn, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  rw [← hn, map_intCast, sub_eq_iff_eq_add.1 hy, map_add, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, map_intCast]
  simp

theorem UpperTheory.V.X.cycKFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], (∀ σ : G ℚ Ω, IsCC σ → cycK Ω l k σ = -1) ∧ ∀ (c : Coef l) (red : c.O →+* k) (g : G ℚ Ω), (cycK Ω l k g : k) = red (chiO ℚ Ω l c.O g : c.O) := by
  intro Ω _ _ _ l hl k _ _
  refine ⟨fun σ hσ => ?_, fun c red g => hom_eq (red.comp (algebraMap ℤ_[l] c.O)) (cycZ ℚ Ω l g : ℤ_[l]ˣ)⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  have h1 : Chr.cls ℚ Ω (l ^ 1) σ = cycMod ℚ Ω l 1 σ := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ =>
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω σ) ζ hζ
  have h2 : Chr.cls ℚ Ω (l ^ 1) σ = -1 := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
  refine Units.ext ?_
  show ZMod.castHom (dvd_pow_self l one_ne_zero) k (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) = _
  rw [← h1, h2]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
