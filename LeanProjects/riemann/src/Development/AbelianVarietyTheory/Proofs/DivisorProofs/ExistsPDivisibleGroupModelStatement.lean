import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivisibleGroupModel
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
theorem _root_.GlobalTheory.T.exists_p_divisible_group_model : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ h : ℕ, (∀ n, Nat.card (Tors G (p ^ n) K) = p ^ (n * h)) → ∃ (GG : PDivGroup p R) (θ : TorsionMap G GG), GG.height = h ∧ IsModel K θ := by
  first | exact @GlobalTheory.GroupBplus.Aff.exists_pDivGroup_isModel | exact GlobalTheory.GroupBplus.Aff.exists_pDivGroup_isModel | (intros; apply GlobalTheory.GroupBplus.Aff.exists_pDivGroup_isModel <;> assumption)
