import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primval
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denint
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.chiFacts :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), Function.Surjective ρ → ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)), Function.Injective (fun ψ : (E ≃ₐ[ℚ] E) →* Oˣ => chiOf ρ ψ) ∧ ∀ (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) (k : ℕ), (chiOf ρ ψ (-1) = (-1) ^ k → chiOf ρ ψ ∈ charSet (PadicAlgCl l) (parE ρ k)) ∧ ∃ a : O, (a : PadicAlgCl l) = alN k (chiOf ρ ψ) := by
  intro E _ _ N _ ρ hρ l _ O
  refine ⟨fun ψ ψ' h => ?_, fun ψ k => ⟨fun hk => ?_, ?_⟩⟩
  · refine MonoidHom.ext fun g => ?_
    obtain ⟨b, rfl⟩ := hρ g
    have hb := congrArg (fun χ : DirichletCharacter (PadicAlgCl l) N => χ (b : ZMod N)) h
    simp only [chiOf_unit] at hb
    exact Units.ext (Subtype.ext hb)
  · simp only [charSet, parE, Set.mem_setOf_eq, Set.mem_inter_iff]
    refine ⟨?_, (b_parity k _).1.2 hk⟩
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, chiOf_unit, hb]
    simp
  · have h := (b_primmem k (chiOf ρ ψ)).2.1 O.toSubring (fun u => by
      rw [chiOf_unit]
      exact (ψ (ρ u) : O).2)
    exact ⟨⟨_, h⟩, rfl⟩
