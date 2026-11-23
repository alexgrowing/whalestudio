import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersion
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_surjective_open_immersion : ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens) (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW → jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part | exact GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part <;> assumption)
