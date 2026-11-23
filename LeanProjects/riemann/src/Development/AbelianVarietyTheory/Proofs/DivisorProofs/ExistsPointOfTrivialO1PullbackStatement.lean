import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointOfTrivialO1Pullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_of_trivial_O1_pullback : ∀ (o k₀ : Type) [CommRing o] [Field k₀] [IsAlgClosed k₀] (b : o →+* k₀) (W : Scheme.{0}) (s : W ⟶ Sp k₀) (n : ℕ) (f : W ⟶ PSpace o n), IsIntegral W → IsProper s → f ≫ PSpace.str o n = s ≫ spMap b → LBIso ((ProjSpace.O1 o n).pull f) (LB.triv W) → ∃ y : Sp k₀ ⟶ PSpace o n, s ≫ y = f := by
  first | exact @GlobalTheory.BdDim.exists_point_of_trivial_O1 | exact GlobalTheory.BdDim.exists_point_of_trivial_O1 | (intros; apply GlobalTheory.BdDim.exists_point_of_trivial_O1 <;> assumption)
