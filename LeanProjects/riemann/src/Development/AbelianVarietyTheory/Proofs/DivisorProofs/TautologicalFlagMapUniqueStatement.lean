import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagMapUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_flag_map_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N)
    (g₁ g₂ : T ⟶ GlobalTheory.FlagZ.Fl ι N) (w₁ : g₁ ≫ GlobalTheory.FlagZ.flStr ι N = g) (w₂ : g₂ ≫ GlobalTheory.FlagZ.flStr ι N = g),
    (∀ a i, ∃ e : (Scheme.Modules.pullback g₁).obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g₁).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g₁ (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w₁).hom.app (GlobalTheory.FlagZ.Taut.stdE N)) →
    (∀ a i, ∃ e : (Scheme.Modules.pullback g₂).obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g₂).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g₂ (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w₂).hom.app (GlobalTheory.FlagZ.Taut.stdE N)) → g₁ = g₂ := by
  first | exact @GlobalTheory.FlagZ.TautUniq.eq_of_pullback_taut | exact GlobalTheory.FlagZ.TautUniq.eq_of_pullback_taut | (intros; apply GlobalTheory.FlagZ.TautUniq.eq_of_pullback_taut <;> assumption)
