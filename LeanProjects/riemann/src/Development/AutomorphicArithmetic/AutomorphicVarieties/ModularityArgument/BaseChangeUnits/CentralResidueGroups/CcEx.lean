import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.EqOfRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Across
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.BiQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

private theorem cc_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let E : IntermediateField ℚ ℂ := j.fieldRange
  let e : Ω ≃ₐ[ℚ] E := AlgEquiv.ofInjectiveField j
  haveI : Normal ℚ E := Normal.of_algEquiv e
  let f : E →ₐ[ℚ] ℂ := ((starRingEnd ℂ).toRatAlgHom).comp E.val
  let g : E ≃ₐ[ℚ] E := f.restrictNormal' E
  have hg : ∀ y : E, ((g y : E) : ℂ) = starRingEnd ℂ (y : ℂ) := fun y => f.restrictNormal_commutes E y
  have he : ∀ x : Ω, ((e x : E) : ℂ) = j x := fun x => rfl
  refine ⟨e.trans (g.trans e.symm), j.toRingHom, fun x => ?_⟩
  show j (e.symm (g (e x))) = starRingEnd ℂ (j x)
  rw [← he, AlgEquiv.apply_symm_apply, hg, he]
