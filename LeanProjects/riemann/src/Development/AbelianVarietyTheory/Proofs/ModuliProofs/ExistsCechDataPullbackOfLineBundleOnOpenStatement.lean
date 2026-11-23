import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCechDataPullbackOfLineBundleOnOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB → ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧ (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧ (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  first | exact @GlobalTheory.LBPush.exists_push | exact GlobalTheory.LBPush.exists_push | (intros; apply GlobalTheory.LBPush.exists_push <;> assumption)
