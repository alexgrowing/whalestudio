import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesOfNaturalNilpotentPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (n d : ℕ) (L : ∀ (S : Type) [CommRing S] [Algebra R S], Prop), (∀ (k m : ℕ), L (Geo.Tor.JetR R (Fin n × Fin d) m ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) m)))) → ∀ (c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin n → Fin d → S) → S), (∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (a : Fin n → Fin d → S), L S → L S' → (∀ y : S, ∃ r : R, IsNilpotent (y - algebraMap R S r)) → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → φ (c S a) = c S' (fun i j => φ (a i j))) → ∃ f : PS R n d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S a = nv (algebraMap R S) f a := by
  first | exact @GlobalTheory.ChF.exists_series_of_natural | exact GlobalTheory.ChF.exists_series_of_natural | (intros; apply GlobalTheory.ChF.exists_series_of_natural <;> assumption)
