import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

namespace GlobalTheory.FrobFilt

theorem mono_of_noEmb_of_injective_genSpecial : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (A C : B.X.Modules) (φ : A ⟶ C), NoEmb B A → (∀ η : B.X, IsGenSpecial B η → Function.Injective (GlobalTheory.QCoh.stalkLinear φ η)) → Mono φ := by
  intro O _ _ _ B A C φ hA hφ
  refine QCoh.mono_of_locally_app_injective _ fun U x hx => ⟨U, hx, le_rfl, fun s t e => ?_⟩
  have H : ∀ η : {η : B.X // η ∈ U ∧ IsGenSpecial B η}, ∃ (W : B.X.Opens) (h : W ≤ U),
      η.1 ∈ W ∧ A.presheaf.map (homOfLE h).op s = A.presheaf.map (homOfLE h).op t := by
    rintro ⟨η, hη, hg⟩
    have h1 : A.presheaf.germ U η hη s = A.presheaf.germ U η hη t := by
      apply hφ η hg
      rw [QCoh.stalkLinear_germ, QCoh.stalkLinear_germ, e]
    obtain ⟨W, hW, i, j, hij⟩ := A.presheaf.germ_eq η hη hη s t h1
    exact ⟨W, i.le, hW, hij⟩
  choose W hWU hW hst using H
  have hV : iSup W ≤ U := iSup_le hWU
  refine hA U (iSup W) hV (fun η hη hg => le_iSup W ⟨η, hη, hg⟩ (hW ⟨η, hη, hg⟩)) ?_
  refine QCoh.section_eq_of_cover A W (le_iSup W) le_rfl _ _ fun η => ?_
  rw [QCoh.res_res, QCoh.res_res]
  exact hst η

end GlobalTheory.FrobFilt
