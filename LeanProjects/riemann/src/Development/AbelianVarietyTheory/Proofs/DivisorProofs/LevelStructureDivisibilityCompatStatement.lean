import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityCompat
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
theorem _root_.GlobalTheory.T.level_structure_divisibility_compat : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N N' : ℕ) (h : N ∣ N'), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A'] (θ : TorsPt G N A) (θ' : TorsPt G N' A'), IsLevel K θ → IsLevel K θ' → ∀ g : A' →ₐc[R] A, (∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), θ'.pt B (torsIncl h z) = (θ.pt B z).comp (g : A' →ₐ[R] A)) → Function.Surjective g := by
  first | exact @GlobalTheory.GroupBplus.Aff.LevSurj.level_surjective | exact GlobalTheory.GroupBplus.Aff.LevSurj.level_surjective | (intros; apply GlobalTheory.GroupBplus.Aff.LevSurj.level_surjective <;> assumption)
