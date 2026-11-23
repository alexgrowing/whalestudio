import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentRankEqOmegaRank
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
theorem _root_.GlobalTheory.T.cotangent_rank_eq_omega_rank : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (GG : PDivGroup p R) (θ : TorsionMap A GG) (c : Pdiv.omega A →ₗ[R] GG.omega), θ.IsOmega c → ∀ (k : Type) [Field k] [Algebra R k] [CharP k p], Module.finrank k (k ⊗[R] Cot R (GG.A 1)) = Module.finrank k (k ⊗[R] Pdiv.omega A) := by
  first | exact @GlobalTheory.GroupBplus.CotRank.finrank_cot_one | exact GlobalTheory.GroupBplus.CotRank.finrank_cot_one | (intros; apply GlobalTheory.GroupBplus.CotRank.finrank_cot_one <;> assumption)
