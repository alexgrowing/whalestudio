import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramesAgreeOnOverlap
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
theorem _root_.GlobalTheory.T.adapted_frames_agree_on_overlap : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V W : T.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (G : ι → GL (Fin N) Γ(T, V)) (H : ι → GL (Fin N) Γ(T, W)),
    Loc.Adapted g fl' V G → Loc.Adapted g fl' W H →
    T.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G =
      T.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ hW.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd H := by
  first | exact @GlobalTheory.FlagZ.Loc.flagPt_inf_eq | exact GlobalTheory.FlagZ.Loc.flagPt_inf_eq | (intros; apply GlobalTheory.FlagZ.Loc.flagPt_inf_eq <;> assumption)
