import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianTypeExtendsNormalScheme
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
theorem _root_.GlobalTheory.T.semiabelian_type_extends_normal_scheme : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X → ∀ (t₀ : SAB H (Sp (Kbar X))), Nonempty (SABMap t₀ tZ (genPt X ≫ g)) → IsOfType Dw t₀ → ∀ (U : AffOp X) (t : SAB H (Sp U.Bp)), Nonempty (SABMap t tZ (U.toX ≫ g)) → ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra U.Bp V] [Algebra V (Kbar X)] [IsScalarTower U.Bp V (Kbar X)] [IsFractionRing V (Kbar X)], spMap (algebraMap U.Bp V) (IsLocalRing.closedPoint V) ∈ abLocus t.G → ∀ (n : ℕ) (z : Tors t.G (p ^ n) (Kbar X)), ∃ z' : Tors t.G (p ^ n) V, torsMap (IsScalarTower.toAlgHom U.Bp V (Kbar X)) z' = z := by
  first | exact @GlobalTheory.GroupBplus.ValExt.exists_torsMap_eq | exact GlobalTheory.GroupBplus.ValExt.exists_torsMap_eq | (intros; apply GlobalTheory.GroupBplus.ValExt.exists_torsMap_eq <;> assumption)
