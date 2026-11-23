import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleSubrep

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

private theorem irr_of_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : IsIrr r)
    (e : RepIso r r') : IsIrr r' :=
  _root_.UpperTheory.Reformulated.B.IrreducibleSubrep.irr_of_iso h e

theorem UpperTheory.V.Z.Bc.autQIso :
    AutQIso := by
  intro F Ω _ _ _ _ l _ ι n r r' e H hc K _ _ _ _ _ _ hK hi
  have e' : RepIso (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))
      (r'.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := by
    obtain ⟨g, hg⟩ := e
    exact ⟨g, fun s => hg _⟩
  obtain ⟨π, h1, -, h3⟩ := H (continuous_of_iso hc e) K hK (irr_of_iso hi e')
  refine ⟨π, h1, (UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n _).2.1 hi, h3.mono fun w hw => ?_⟩
  obtain ⟨B, hB, hE⟩ := hw
  exact ⟨B, hB, hE.of_iso e'.symm'⟩
