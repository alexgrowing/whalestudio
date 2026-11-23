import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTypeExtendsAffineNormal
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
theorem _root_.GlobalTheory.T.generic_type_extends_affine_normal : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X → ∀ (t₀ : SAB H (Sp (Kbar X))), Nonempty (SABMap t₀ tZ (genPt X ≫ g)) → IsOfType Dw t₀ → ∀ (U : AffOp X) (t : SAB H (Sp U.Bp)), Nonempty (SABMap t tZ (U.toX ≫ g)) → ∀ (GG : PDivGroup p U.Bp) (θ : TorsionMap t.G GG), IsModel (Kbar X) θ → θ.IsIsoOver (abLocus t.G) := by
  first | exact @GlobalTheory.GroupBplus.Aff.isIsoOver_abLocus_of_isModel | exact GlobalTheory.GroupBplus.Aff.isIsoOver_abLocus_of_isModel | (intros; apply GlobalTheory.GroupBplus.Aff.isIsoOver_abLocus_of_isModel <;> assumption)
