import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.CBC.SatakeParameterExistence

theorem re {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (π : UpperTheory.V.TR.CuspSub F n) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat v B :=
  UpperTheory.V.Af.Gk.satAE F n π

theorem cx (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ)
    (π : CuspSub F n) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B := by
  simpa only [CG.hasSat_mk] using UnrSat.eventually_hasSatGL_locRep hF F n π

theorem of_fin (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) : UpperTheory.CBC.SSatEx := by
  intro F _ _ n π
  match π with
  | @Cusp.cx _ _ _ _ hC π => exact cx hF n π
  | @Cusp.re _ _ _ _ hR π => exact re n π

end UpperTheory.CBC.SatakeParameterExistence
