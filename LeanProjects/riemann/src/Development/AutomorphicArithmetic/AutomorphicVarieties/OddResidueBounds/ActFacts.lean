import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.actFacts :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → Function.Surjective ρ ∧ IsAbelianGalois ℚ E ∧ Nat.card (Gq ρ) = Module.finrank ℚ E ∧ ρ.ker.index = Module.finrank ℚ E ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), IsCycAct Ω M (ρ.comp (ZMod.unitsMap h)) := by
  intro E Ω _ _ _ _ _ N _ ρ hρ
  obtain ⟨_, hb⟩ := liftEx E Ω N
  have inj := (algebraMap E Ω).injective
  have hsurj : Function.Surjective ρ := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_isLift (Ω := Ω) τ.toRingEquiv
    obtain ⟨b, hbσ⟩ := hb σ
    refine ⟨b, ?_⟩
    ext x
    apply inj
    have h1 := hρ b σ hbσ x
    have h2 := hσ x
    simpa using h1.symm.trans h2
  haveI hc : CharZero Ω := charZero_of_injective_algebraMap inj
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ φ : E →ₐ[ℚ] Ω, ∃ σ : Ω ≃+* Ω, ∀ x : E, σ (algebraMap E Ω x) = φ x := by
    intro φ
    refine ⟨((Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ Ω).symm (φ.liftNormal Ω)).toRingEquiv,
      fun x => ?_⟩
    have h := φ.liftNormal_commutes Ω x
    simpa using h
  let f : Gal(E/ℚ) → (E →ₐ[ℚ] Ω) := fun g => (IsScalarTower.toAlgHom ℚ E Ω).comp g.toAlgHom
  have hf : Function.Surjective f := by
    intro φ
    obtain ⟨σ, hσ⟩ := key φ
    obtain ⟨b, hbσ⟩ := hb σ
    refine ⟨ρ b, ?_⟩
    ext x
    have h1 := hρ b σ hbσ x
    rw [← hσ x, h1]
    rfl
  have hcard : Nat.card Gal(E/ℚ) = Module.finrank ℚ E := by
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    · calc Module.finrank ℚ E = Nat.card (E →ₐ[ℚ] Ω) := by
            rw [Nat.card_eq_fintype_card, AlgHom.card]
        _ ≤ Nat.card Gal(E/ℚ) := Nat.card_le_card_of_surjective f hf
  haveI : IsGalois ℚ E := IsGalois.of_card_aut_eq_finrank ℚ E hcard
  have hq : Nat.card (Gq ρ) = Module.finrank ℚ E := by
    rw [← hcard]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).toEquiv
  refine ⟨hsurj, ?_, hq, hq, ?_⟩
  · exact
      { is_comm := ⟨fun x y => by
          obtain ⟨a, rfl⟩ := hsurj x
          obtain ⟨c, rfl⟩ := hsurj y
          rw [← map_mul, ← map_mul, mul_comm]⟩ }
  · intro M _ h b σ hσ
    apply hρ
    intro x hx
    have hxM : x ^ M = 1 := by
      obtain ⟨k, rfl⟩ := h
      rw [pow_mul, hx, one_pow]
    rw [hσ x hxM, ZMod.unitsMap_val]
    have e : (ZMod.cast (b : ZMod M) : ZMod N).val = (b : ZMod M).val % N := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (b : ZMod M)]
      rw [ZMod.cast_natCast h, ZMod.val_natCast]
    rw [e]
    conv_lhs => rw [← Nat.div_add_mod (b : ZMod M).val N]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
