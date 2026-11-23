import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueCoeffsStableBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_coeffs_stable_basis : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α : D.X) (m : ℕ) (b : Fin m → D.SecB k α),
    GlobalTheory.IntFam.StableBasis D k α b → ∀ s : SecAbF D (FractionRing R) k α,
      ∃! c : Fin m → FractionRing R, s = ∑ i, c i • pullAb D (FractionRing R) k α (b i) := by
  first | exact @GlobalTheory.IntFam.exists_unique_coord_generic | exact GlobalTheory.IntFam.exists_unique_coord_generic | (intros; apply GlobalTheory.IntFam.exists_unique_coord_generic <;> assumption)
