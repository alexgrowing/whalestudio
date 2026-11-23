import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion : (∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : ℕ) (σ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => g.pG.left) (fun _ => (k : ℤ)))), ∃! f : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)), ∃ s : Finset D.X, (∀ α ∉ s, ∀ j, (f α).f j = 0) ∧ ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J → sval σ (𝟙 (thickObj R I e G).left) z J = ∑ α ∈ s, sval (f α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val) := by
  first | exact @GlobalTheory.existsUnique_level_expansion | exact GlobalTheory.existsUnique_level_expansion | (intros; apply GlobalTheory.existsUnique_level_expansion <;> assumption)
