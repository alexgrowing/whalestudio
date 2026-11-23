import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.Lk.liftO :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (χ : Γ →* (PadicAlgCl l)ˣ), Continuous χ → (∀ g, (χ g : PadicAlgCl l) ∈ c.O) → ∃ χ' : Γ →* c.Oˣ, toQ χ' = χ ∧ (AdicCont (maximalIdeal c.O) fun g => (χ' g : c.O)) ∧ ∀ g, ‖(χ g : PadicAlgCl l) - 1‖ < 1 → residue c.O (χ' g) = 1 := by
  intro l _ c Γ _ _ χ hχ hO
  have hinv : ∀ g, (χ g : PadicAlgCl l) * (χ g⁻¹ : PadicAlgCl l) = 1 := by
    intro g
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hinv' : ∀ g, (χ g⁻¹ : PadicAlgCl l) * (χ g : PadicAlgCl l) = 1 := by
    intro g
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  let u : Γ → c.Oˣ := fun g =>
    ⟨⟨χ g, hO g⟩, ⟨χ g⁻¹, hO g⁻¹⟩, Subtype.ext (hinv g), Subtype.ext (hinv' g)⟩
  let χ' : Γ →* c.Oˣ :=
    { toFun := u
      map_one' := by
        ext
        simp [u]
      map_mul' := by
        intro a b
        ext
        simp [u] }
  have hval : ∀ g, ((χ' g : c.O) : PadicAlgCl l) = χ g := fun g => rfl
  refine ⟨χ', ?_, ?_, ?_⟩
  · ext g
    rfl
  · rw [(X.So.adicCont l c).2 Γ]
    exact Continuous.subtype_mk (Units.continuous_val.comp hχ) _
  · intro g hg
    rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub, residue_eq_zero_iff,
      (Fr.sc_norm l c _).2]
    simpa [hval] using hg
