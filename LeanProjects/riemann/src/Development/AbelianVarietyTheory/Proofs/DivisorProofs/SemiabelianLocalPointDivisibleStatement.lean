import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLocalPointDivisible
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
theorem _root_.GlobalTheory.T.semiabelian_local_point_divisible : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (q : PrimeSpectrum R) (x : SpAlg R (Localization.AtPrime q.asIdeal) ⟶ G) (m : ℕ), m ≠ 0 → ∃ y, y ^ m = x := by
  first | exact @GlobalTheory.GroupBplus.Aff.Divis.exists_pow_eq | exact GlobalTheory.GroupBplus.Aff.Divis.exists_pow_eq | (intros; apply GlobalTheory.GroupBplus.Aff.Divis.exists_pow_eq <;> assumption)
