import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramesAgreeOnOverlapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeMorphismsGlueOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulesIsoOfMatchingFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTautologicalFrameStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB GlobalTheory.FlagZ

namespace GlobalTheory.FlagZ

theorem exists_classifying : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    ∃ g' : T ⟶ GlobalTheory.FlagZ.Fl ι N, ∃ w : g' ≫ GlobalTheory.FlagZ.flStr ι N = g, ∀ a i,
      ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g' (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w).hom.app (GlobalTheory.FlagZ.Taut.stdE N) := by
  intro ι _ N fl hfl T g fl'
  choose V hxV hV G hG using fun t : T => GlobalTheory.T.flag_locally_adapted_affine_frame g fl' t
  have hU : ⨆ t, V t = ⊤ := top_le_iff.1 fun t _ => TopologicalSpace.Opens.mem_iSup.2 ⟨t, hxV t⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.T.scheme_morphisms_glue_open_cover V hU
    (fun t => (hV t).isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (G t))
    fun k l => GlobalTheory.T.adapted_frames_agree_on_overlap g fl' (V k) (V l) (hV k) (hV l) (G k) (G l) (hG k) (hG l)
  have w : g' ≫ flStr ι N = g := toZ_ext _ _
  refine ⟨g', w, fun a i => ?_⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.modules_iso_of_matching_frames ((Scheme.Modules.pullback g').map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)) ((fl' a).ι i) i fun x => by
    obtain ⟨s₁, hs₁, e₁⟩ := GlobalTheory.T.flag_point_tautological_frame ι N fl hfl T g g' w (V x) (hV x) (G x) (hg' x) a i
    obtain ⟨s₂, hs₂, e₂⟩ := hG x a i
    exact ⟨V x, s₁, s₂, hxV x, hs₁, hs₂, fun j => (e₁ j).trans (e₂ j).symm⟩
  exact ⟨e, he⟩

end GlobalTheory.FlagZ
