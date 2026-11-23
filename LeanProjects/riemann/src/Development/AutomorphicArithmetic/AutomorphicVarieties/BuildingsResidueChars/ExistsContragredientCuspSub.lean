import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin)
open scoped Matrix

theorem UpperTheory.exists_contragredient_cuspSub :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∃ π₂ : TR.CuspSub F a, (∃ S : π.V ≃ₗ[ℂ] π₂.V, (∀ k φ, π₂.op (.fin k) (S φ) = S (π.op (.fin (invT a (Af F) k)) φ)) ∧
          (∀ k φ, π₂.op (.cpt k) (S φ) = S (π.op (.cpt k) φ)) ∧
          ∀ X φ, π₂.op (.lie X) (S φ) = S (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) φ)) ∧
        (∀ v m, π.HasInfChar v m → π₂.HasInfChar v (m.map Neg.neg)) ∧ ∀ w B, π.HasSat w B → π₂.HasSat w (B.map (·⁻¹)) := by
  intro F _ _ _ a π
  exact ⟨π.dual, ⟨π.toDual, fun k φ => π.op_toDual (.fin k) φ, fun k φ => π.op_toDual (.cpt k) φ,
    fun X φ => π.op_toDual (.lie X) φ⟩, fun _ _ h => h.dual, fun _ _ h => h.dual⟩
