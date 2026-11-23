import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionKernelFinitePresentation
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
theorem _root_.GlobalTheory.T.torsion_points_eq_of_local : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (B : Type) [CommRing B] [Algebra R B], ∀ z z' : Tors G N B, (∀ P : PrimeSpectrum B, ∃ f : B, f ∉ P.asIdeal ∧ torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z = torsMap (IsScalarTower.toAlgHom R B (Localization.Away f)) z') → z = z' := by
  first | exact @GlobalTheory.GroupBplus.Aff.tors_ext_of_local | exact GlobalTheory.GroupBplus.Aff.tors_ext_of_local | (intros; apply GlobalTheory.GroupBplus.Aff.tors_ext_of_local <;> assumption)
