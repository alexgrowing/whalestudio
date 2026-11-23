import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_i6_of_reference : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper | exact GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper <;> assumption)
