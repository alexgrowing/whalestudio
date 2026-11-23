import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureMultiplicationMap
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
theorem _root_.GlobalTheory.T.level_structure_multiplication_map : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N m : ℕ), N ≠ 0 → m ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A'] (θ : TorsPt G N A) (θ' : TorsPt G (N * m) A'), IsLevel K θ → IsLevel K θ' → ∀ g : A' →ₐc[R] A, (∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), θ'.pt B (torsIncl (Dvd.intro m rfl) z) = (θ.pt B z).comp (g : A' →ₐ[R] A)) → RingHom.ker (g : A' →ₐ[R] A) = torsionIdeal R A' N := by
  first | exact @GlobalTheory.GroupBplus.Aff.LevKer.ker_eq_torsionIdeal | exact GlobalTheory.GroupBplus.Aff.LevKer.ker_eq_torsionIdeal | (intros; apply GlobalTheory.GroupBplus.Aff.LevKer.ker_eq_torsionIdeal <;> assumption)
