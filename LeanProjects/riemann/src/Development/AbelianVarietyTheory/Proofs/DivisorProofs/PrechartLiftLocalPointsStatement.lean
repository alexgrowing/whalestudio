import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartLiftLocalPoints
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
theorem _root_.GlobalTheory.T.prechart_lift_local_points : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (x : Tors G N B), Set.range (torsMap (IsScalarTower.toAlgHom R B (IsLocalRing.ResidueField B)) x).1.left ⊆ c.W → ∃ ψ : c.C →ₐ[R] B, torsMap ψ c.j = x := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_chart_of_residue | exact GlobalTheory.GroupBplus.Aff.exists_chart_of_residue | (intros; apply GlobalTheory.GroupBplus.Aff.exists_chart_of_residue <;> assumption)
