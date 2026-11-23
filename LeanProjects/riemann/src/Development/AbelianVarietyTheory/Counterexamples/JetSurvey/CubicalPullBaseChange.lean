import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.GtBaseChangeSharp
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.CubeMapTripleProductUnique
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.GroupHomPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeConclusionIff

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext exists_chart gm_cocycle gm_self glue_unit)
open GlobalTheory.GtCubeCompare (gw PM maps_iff_pm)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubePullLawChecks

section General

variable {X Y : Scheme.{0}} {A B C : LB X}

end General

theorem rigPullIsGen : RigPullIsGenSt.{0} := by
  intro S S' G' G _ _ _ _ F e he L r _ hr
  exact Out.LBxP.isGen_pullAlong L F e (fun _ : PUnit => eSec G) (fun _ => 1)
    (fun _ => eSec G') (fun _ => he) r hr

end GlobalTheory.CubePullLawChecks

end
