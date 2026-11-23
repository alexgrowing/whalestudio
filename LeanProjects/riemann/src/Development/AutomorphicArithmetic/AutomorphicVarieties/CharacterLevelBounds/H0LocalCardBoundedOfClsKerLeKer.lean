import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0Nu
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NuLeBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.H0_local_card_bounded_of_cls_ker_le_ker :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → (cls ℚ Ω N).ker ≤ ψ.ker →
          (∀ (A : ValuationSubring Ω) (U : Subgroup (G ℚ Ω)), A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ U →
            h0 l e ψ U ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O) ∧ h0 l e ψ ⊤ ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O := by
  intro Ω _ _ _ l hl O _ _ _ _ _ N _ e ψ he hψ
  have key : ∀ (A : ValuationSubring Ω) (U : Subgroup (G ℚ Ω)), A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ U →
      h0 l e ψ U ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O := by
    intro A U hA hU
    have h1 := (h0Nu ℚ Ω l O e ψ U).1 (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker) (inf_le_left.trans hU)
    have h2 := (h0Nu ℚ Ω l O e ψ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker)).2 (inf_le_right.trans hψ)
    have h3 := LDataCardLeFinrank.nuLeBound l N e _ ((clsOnto Ω N).2 l A hA) he
    exact h1.trans (h2.trans (mul_le_mul_left h3 _))
  obtain ⟨A, hA⟩ := (placesQ Ω).1 l hl.out
  exact ⟨key, key A ⊤ hA le_top⟩
