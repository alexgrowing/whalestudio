import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureHopf
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
theorem _root_.GlobalTheory.T.exists_level_structure_hopf : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra R A) (_ : IsCocomm R A) (_ : Module.Finite R A) (_ : Module.Projective R A) (θ : TorsPt G N A), IsLevel K θ := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_level | exact GlobalTheory.GroupBplus.Aff.exists_level | (intros; apply GlobalTheory.GroupBplus.Aff.exists_level <;> assumption)
