import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionClosedFibreOfPrimitiveTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_closed_fibre_of_primitive_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  first | exact @GlobalTheory.UMin.exists_sec_nz_of_prim | exact GlobalTheory.UMin.exists_sec_nz_of_prim | (intros; apply GlobalTheory.UMin.exists_sec_nz_of_prim <;> assumption)
