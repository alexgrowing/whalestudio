import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_cell_coordinates_exist : ∀ (K : Type) [Field K] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → K) (u : Fin k → Fin (N + 1) → K), a ≤ k → k ≤ b → LeftInv D c → LinearIndependent K u → initSpan K c a ≤ Submodule.span K (Set.range u) → Submodule.span K (Set.range u) ≤ initSpan K c b → (∃ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0 → ∃ x : GVar m a k b → K, Submodule.span K (Set.range u) = initSpan K (gvec c w x) k := by
  first | exact @GlobalTheory.GrCl.Normal.main | exact GlobalTheory.GrCl.Normal.main | (intros; apply GlobalTheory.GrCl.Normal.main <;> assumption)
