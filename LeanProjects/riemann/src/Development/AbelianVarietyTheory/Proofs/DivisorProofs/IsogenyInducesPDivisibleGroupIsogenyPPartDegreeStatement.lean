import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  first | exact @GlobalTheory.Dieu.isIsog_hasLogDeg_map | exact GlobalTheory.Dieu.isIsog_hasLogDeg_map | (intros; apply GlobalTheory.Dieu.isIsog_hasLogDeg_map <;> assumption)
