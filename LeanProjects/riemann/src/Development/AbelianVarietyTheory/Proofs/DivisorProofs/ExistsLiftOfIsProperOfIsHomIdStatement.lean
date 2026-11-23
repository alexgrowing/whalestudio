import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfIsProperOfIsHomId
import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_isProper_of_isHom_id' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  first | exact @GlobalTheory.exists_lift_of_isProper_of_isHom_id | exact GlobalTheory.exists_lift_of_isProper_of_isHom_id | (intros; apply GlobalTheory.exists_lift_of_isProper_of_isHom_id <;> assumption)
