import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalTheta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta : ∀ {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r => GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  first | exact @GlobalTheory.TensBal.SpanPf.main | exact GlobalTheory.TensBal.SpanPf.main | (intros; apply GlobalTheory.TensBal.SpanPf.main <;> assumption)
