import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentOfDefectKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareBundle_descent_of_defect_killed : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f M φ → Defect f M φ D → KillsSq f D u → ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ), M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  first | exact @GlobalTheory.SqDatum.exists_sq_descent | exact GlobalTheory.SqDatum.exists_sq_descent | (intros; apply GlobalTheory.SqDatum.exists_sq_descent <;> assumption)
