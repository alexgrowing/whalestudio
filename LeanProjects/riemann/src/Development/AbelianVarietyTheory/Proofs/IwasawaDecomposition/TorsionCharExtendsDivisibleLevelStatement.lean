import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionChar_extends_divisible_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q q' : ℕ), q' ≠ 0 → q ∣ q' → ∀ c : TorsChar t x q, ∃ c' : TorsChar t x q', ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = c.χ B w := by
  first | exact @GlobalTheory.TorsCharExt.exists_extension | exact GlobalTheory.TorsCharExt.exists_extension | (intros; apply GlobalTheory.TorsCharExt.exists_extension <;> assumption)
