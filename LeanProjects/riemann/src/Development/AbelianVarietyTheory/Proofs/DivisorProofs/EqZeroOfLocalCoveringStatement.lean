import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLocalCovering
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
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
theorem _root_.GlobalTheory.T.torsion_point_generic_fibre_range : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (P : PrimeSpectrum B), z.1.left P ∈ Set.range (torsMap (IsScalarTower.toAlgHom R B (FractionRing (B ⧸ P.asIdeal))) z).1.left := by
  first | exact @GlobalTheory.GroupBplus.Aff.tors_point_range_fld | exact GlobalTheory.GroupBplus.Aff.tors_point_range_fld | (intros; apply GlobalTheory.GroupBplus.Aff.tors_point_range_fld <;> assumption)
