import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLiftStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.LiftRef

theorem liftAll_of_parIn : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, ParIn hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  intro hP hL
  have h := overRows_and_mono (GlobalTheory.T.twist_character_unramified_inf hP hL) (GlobalTheory.T.isotypic_real_nonzero hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  have h' := overRows_and_mono h (GlobalTheory.T.spherical_inertia_of_isotypic hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  refine overRows_and_mono h' (GlobalTheory.T.infinity_type_of_lift hP hL) ?_
  rintro K B f T w Z Wt hX z p0 Y ⟨⟨hc, hl⟩, hs⟩ hi Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨S, hS, hm, hloc⟩ := hl Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨μ, hμ, hcsd, hunr, heta⟩ := hc Rw a M tup Q hA hI ⟨j - 1, by omega⟩
  exact ⟨_, μ, ⟨hcsd, hunr, hs Rw a M tup Q hA hI j h1 h2 S hS hm, hloc μ hμ, heta, hi Rw a M tup Q hA hI j h1 h2 S hS μ hμ⟩⟩

end GlobalTheory.LiftRef
