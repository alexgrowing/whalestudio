import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLocalPoints
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
theorem _root_.GlobalTheory.T.level_structure_local_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (θ : TorsPt G N A), IsLevel K θ → ∀ (B : Type) [CommRing B] [Algebra R B] [IsLocalRing B] (φ : A →ₐ[R] B), ∃ (z : Tors G N B) (s : A →ₐ[R] R), toConv φ = toConv (θ.pt B z) * toConv ((Algebra.ofId R B).comp s) := by
  first | exact @GlobalTheory.GroupBplus.Aff.level_point_eq_tors_mul_section | exact GlobalTheory.GroupBplus.Aff.level_point_eq_tors_mul_section | (intros; apply GlobalTheory.GroupBplus.Aff.level_point_eq_tors_mul_section <;> assumption)
