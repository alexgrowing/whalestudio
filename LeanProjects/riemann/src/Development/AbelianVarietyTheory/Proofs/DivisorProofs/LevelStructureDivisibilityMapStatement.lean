import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDivisibilityMap
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
theorem _root_.GlobalTheory.T.level_structure_divisibility_map : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N N' : ℕ), N ≠ 0 → N ∣ N' → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A'] (θ : TorsPt G N A) (θ' : TorsPt G N' A'), IsLevel K θ → IsLevel K θ' → ∀ f : G ⟶ G, IsMonHom f → ∃! g : A' →ₐc[R] A, ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (z' : Tors G N' B), z'.1 = z.1 ≫ f → θ'.pt B z' = (θ.pt B z).comp (g : A' →ₐ[R] A) := by
  first | exact @GlobalTheory.GroupBplus.Aff.LevMap.existsUnique_bialgHom_of_levels | exact GlobalTheory.GroupBplus.Aff.LevMap.existsUnique_bialgHom_of_levels | (intros; apply GlobalTheory.GroupBplus.Aff.LevMap.existsUnique_bialgHom_of_levels <;> assumption)
