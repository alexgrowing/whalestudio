import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingClosedAllFibres
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_embedding_closed_all_fibres : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → ∀ (W : Scheme.{0}) [IsIntegral W] [IsLocallyNoetherian W] (G : Over W) [GrpObj G], IsSemiAbelian G → ∀ (r : ℕ) (u : splitTorus W (Fin r → ℤ) ⟶ G), IsMonHom u → (∀ (k : Type) [Field k] (g : Sp k ⟶ W), g (IsLocalRing.closedPoint k) = genericPoint W → IsClosedImmersion ((Over.pullback g).map u).left) → ∀ (k : Type) [Field k] (w : Sp k ⟶ W), IsClosedImmersion ((Over.pullback w).map u).left := by
  first | exact @GlobalTheory.TorusFibreImm.isClosedImmersion_fibre | exact GlobalTheory.TorusFibreImm.isClosedImmersion_fibre | (intros; apply GlobalTheory.TorusFibreImm.isClosedImmersion_fibre <;> assumption)
