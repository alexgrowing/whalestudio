import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_mu :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M a : ℕ), M ≠ 0 → ∀ (C : Type) [Group C] (χ : G ℚ Ω →* C), Af.KillsMu (M ^ a) χ → IsOpen (χ.ker : Set (G ℚ Ω)) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ χ.ker := by
  intro Ω _ _ _ M a hM C _ χ hk
  haveI : NeZero (M ^ a) := ⟨pow_ne_zero _ hM⟩
  obtain ⟨hopen, -, -, -, hine⟩ := UpperTheory.V.Chr.clsFacts ℚ Ω (M ^ a)
  have hle : (UpperTheory.V.Chr.cls ℚ Ω (M ^ a)).ker ≤ χ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply hk s
    intro ζ hζ
    rw [UpperTheory.V.Chr.cls_spec (M ^ a) s ζ hζ, hs, Units.val_one, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod 1 hζ, pow_one]
  refine ⟨Subgroup.isOpen_mono hle hopen, ?_⟩
  intro A hA
  refine le_trans (hine A ?_) hle
  rw [Nat.cast_pow, map_pow, not_lt]
  exact one_le_pow₀ (not_lt.mp hA)
