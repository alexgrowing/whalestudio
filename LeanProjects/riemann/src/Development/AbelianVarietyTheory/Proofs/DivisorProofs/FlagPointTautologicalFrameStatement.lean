import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTautologicalFrame
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
theorem _root_.GlobalTheory.T.flag_point_tautological_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (g' : T ⟶ Fl ι N) (w : g' ≫ flStr ι N = g) (V : T.Opens) (hV : IsAffineOpen V)
    (G : ι → GL (Fin N) Γ(T, V)), V.ι ≫ g' = hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G →
    ∀ (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback g').obj ((fl a).F l), V), IsFrame s ∧ ∀ j,
      ((Scheme.Modules.pullback g').map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)).app V (s j) =
        Loc.colSecOn g V (G a).1 (Fin.castLE l.is_le j) := by
  first | exact @GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut | exact GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut | (intros; apply GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut <;> assumption)
