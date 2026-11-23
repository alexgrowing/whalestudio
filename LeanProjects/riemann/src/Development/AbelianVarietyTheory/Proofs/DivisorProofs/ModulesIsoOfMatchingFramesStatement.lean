import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulesIsoOfMatchingFrames
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modules_iso_of_matching_frames : ∀ {X : Scheme.{0}} {F₁ F₂ E : X.Modules} (m₁ : F₁ ⟶ E) (m₂ : F₂ ⟶ E) [Mono m₂] (r : ℕ),
    (∀ x : X, ∃ (U : X.Opens) (s₁ : Fin r → Γ(F₁, U)) (s₂ : Fin r → Γ(F₂, U)), x ∈ U ∧ IsFrame s₁ ∧ IsFrame s₂ ∧
      ∀ j, m₁.app U (s₁ j) = m₂.app U (s₂ j)) →
    ∃ e : F₁ ≅ F₂, e.hom ≫ m₂ = m₁ := by
  first | exact @GlobalTheory.VB.exists_iso_of_frames_app_eq | exact GlobalTheory.VB.exists_iso_of_frames_app_eq | (intros; apply GlobalTheory.VB.exists_iso_of_frames_app_eq <;> assumption)
