import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslate
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_translate_iso_cubical : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L → ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  first | exact @GlobalTheory.Mum.lam_transl_iso | exact GlobalTheory.Mum.lam_transl_iso | (intros; apply GlobalTheory.Mum.lam_transl_iso <;> assumption)
