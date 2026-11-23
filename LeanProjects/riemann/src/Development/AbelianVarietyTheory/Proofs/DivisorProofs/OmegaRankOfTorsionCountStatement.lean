import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaRankOfTorsionCount
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
theorem _root_.GlobalTheory.T.omega_rank_of_torsion_count : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (spMap (algebraMap R K))) → ∀ (p g : ℕ), p.Prime → Nat.card (Tors G p K) = p ^ (2 * g) → ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] Pdiv.omega G) = g := by
  first | exact @GlobalTheory.OmegaRankGen.finrank_omega | exact GlobalTheory.OmegaRankGen.finrank_omega | (intros; apply GlobalTheory.OmegaRankGen.finrank_omega <;> assumption)
