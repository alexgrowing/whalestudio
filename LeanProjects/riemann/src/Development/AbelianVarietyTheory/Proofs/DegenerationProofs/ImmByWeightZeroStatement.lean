import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZero
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.immBy_weight_zero' : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → ImmBy Φ.G.hom (Φ.H 1) F {i | cls i = 0}) := by
  first | exact @GlobalTheory.ZH.ClosedImm.immBy_weight_zero | exact GlobalTheory.ZH.ClosedImm.immBy_weight_zero | (intros; apply GlobalTheory.ZH.ClosedImm.immBy_weight_zero <;> assumption)
