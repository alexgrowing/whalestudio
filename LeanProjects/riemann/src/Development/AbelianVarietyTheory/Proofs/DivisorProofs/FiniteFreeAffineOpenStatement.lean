import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeAffineOpen
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
theorem _root_.GlobalTheory.T.torsion_point_open_localization : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (C D : Type) [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (ψ : C →ₐ[R] D) (j : Tors G N C) (W : G.left.Opens) (P : PrimeSpectrum D), (torsMap ψ j).1.left P ∈ W → ∃ e : C, ψ e ∉ P.asIdeal ∧ Set.range (torsMap (IsScalarTower.toAlgHom R C (Localization.Away e)) j).1.left ⊆ W := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_away_range_torsMap_subset | exact GlobalTheory.GroupBplus.Aff.exists_away_range_torsMap_subset | (intros; apply GlobalTheory.GroupBplus.Aff.exists_away_range_torsMap_subset <;> assumption)
