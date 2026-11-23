import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinesCompAndMul
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
theorem _root_.GlobalTheory.T.intertwines_comp_and_mul : ∀ (p : ℕ) (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (GG : PDivGroup p R) (θ : TorsionMap A GG), θ.Intertwines (𝟙 A) (𝟙 GG) ∧ (∀ (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'] (g g' : GG ⟶ GG), θ.Intertwines f g → θ.Intertwines f' g' → θ.Intertwines (f ≫ f') (g ≫ g')) ∧ ∀ (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'] (g g' : GG ⟶ GG), θ.Intertwines f g → θ.Intertwines f' g' → θ.Intertwines (f * f') (g + g') := by
  first | exact @GlobalTheory.GroupBplus.Aff.intertwines_rules | exact GlobalTheory.GroupBplus.Aff.intertwines_rules | (intros; apply GlobalTheory.GroupBplus.Aff.intertwines_rules <;> assumption)
