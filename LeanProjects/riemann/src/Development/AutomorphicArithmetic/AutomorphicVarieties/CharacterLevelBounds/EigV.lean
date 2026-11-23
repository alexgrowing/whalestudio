import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelEigBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.eigV :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)) [U.Normal],
          IsOpen (U : Set (G k Ω)) → U ≤ ψ.ker → ¬ l ∣ U.index → eigL l e U ψ = V l e ψ := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U _ hU hker hind
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l O
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    have hk : (ψ⁻¹).ker = ψ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact Subgroup.isOpen_mono hker hU
  have hcont := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  unfold eigL V VS
  exact selEigBase O (G k Ω) (QO l O) _ (rho l e ψ) ψ (tw_apply l e ψ) hcont U ⊤ le_top
    (fun u hu => hker hu) (hU.preimage continuous_subtype_val)
    (by rw [Subgroup.relIndex_top_right]; exact hunit _ hind) _ (conjStable_shaFam k Ω l)
