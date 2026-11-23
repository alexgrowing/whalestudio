import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagUniversalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagMapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagGradedIsometricStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagZ.Taut

theorem isFlagBundle_std_isometric : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (E : ι → (Sp ℤ).Modules) (h : ∀ a, VMetric (𝟙 (Sp ℤ)) (E a) N) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (E a)) N), IsFlagBundle (GlobalTheory.FlagZ.flStr ι N) E (fun _ => N) fl ∧ ∀ (a : ι) (i : Fin N), (VMetric.grLB (fl a) i ((H a).pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))).Isometric (GlobalTheory.FlagZ.grLine (a, i)) := by
  intro ι _ N
  obtain ⟨fl, hfl⟩ := GlobalTheory.T.tautological_flag_exists ι N
  refine ⟨fun _ => stdE N, fun _ => (HermVB.std (𝟙 (Sp ℤ)) N).h, fun _ => (HermVB.std (𝟙 (Sp ℤ)) N).cInf, fl,
    fun T g fl' => ?_, fun a i => GlobalTheory.T.tautological_flag_graded_isometric ι N fl hfl a i⟩
  obtain ⟨g', w, he⟩ := GlobalTheory.T.tautological_flag_universal ι N fl hfl T g fl'
  exact ⟨g', ⟨w, he⟩, fun g'' ⟨w'', he''⟩ => GlobalTheory.T.tautological_flag_map_unique ι N fl hfl T g fl' g'' g' w'' w he'' he⟩

end GlobalTheory.FlagZ.Taut
