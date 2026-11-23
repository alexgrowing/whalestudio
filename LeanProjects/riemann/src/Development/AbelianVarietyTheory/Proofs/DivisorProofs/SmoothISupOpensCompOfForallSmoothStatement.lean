import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth : ∀ (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens), (∀ i, Smooth ((V i).ι ≫ q)) → Smooth ((⨆ i, V i).ι ≫ q) := by
  first | exact @GlobalTheory.Mum.smooth_iSup_comp | exact GlobalTheory.Mum.smooth_iSup_comp | (intros; apply GlobalTheory.Mum.smooth_iSup_comp <;> assumption)
