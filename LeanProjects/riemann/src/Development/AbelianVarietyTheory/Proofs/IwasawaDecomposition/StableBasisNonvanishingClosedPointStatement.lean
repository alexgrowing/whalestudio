import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableBasisNonvanishingClosedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_basis_nonvanishing_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (m : ℕ)
    (b : Fin m → SecAb D k α), GlobalTheory.IntFam.StableBasis D k α b → ∀ c : Fin m → R, (∃ i, c i ∉ maximalIdeal R) →
      ∃ (j : Fin 4 → D.P.L.ι) (y : D.P.A.left), D.P.A.hom y = closedPoint R ∧
        y ∈ D.P.A.left.basicOpen ((∑ i, c i • b i).f j) := by
  first | exact @GlobalTheory.IntFam.exists_closed_mem_basicOpen_of_stableBasis | exact GlobalTheory.IntFam.exists_closed_mem_basicOpen_of_stableBasis | (intros; apply GlobalTheory.IntFam.exists_closed_mem_basicOpen_of_stableBasis <;> assumption)
