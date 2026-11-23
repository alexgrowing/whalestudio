import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_torus_after_separable : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G)) := by
  first | exact @GlobalTheory.exists_finite_separable_torusExtension | exact GlobalTheory.exists_finite_separable_torusExtension | (intros; apply GlobalTheory.exists_finite_separable_torusExtension <;> assumption)
