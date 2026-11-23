import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionChartRangeInjectiveEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_chart_range_injective_embedding : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSeparated G.hom → ∀ (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (B : Type) [CommRing B] [IsDomain B] [Algebra R B], IsUnit (algebraMap R B c.r) → ∀ (em : B →ₐ[R] K), Function.Injective em → ∀ z : Tors G N B, Set.range (torsMap em z).1.left ⊆ c.W → Set.range z.1.left ⊆ c.W := by
  first | exact @GlobalTheory.GroupBplus.Aff.PreChart.range_subset_of_generic | exact GlobalTheory.GroupBplus.Aff.PreChart.range_subset_of_generic | (intros; apply GlobalTheory.GroupBplus.Aff.PreChart.range_subset_of_generic <;> assumption)
