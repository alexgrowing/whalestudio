import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCover
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_iSup_of_uniformisationParameters_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  first | exact @GlobalTheory.CechPer.le_iSup_of_pre_cover | exact GlobalTheory.CechPer.le_iSup_of_pre_cover | (intros; apply GlobalTheory.CechPer.le_iSup_of_pre_cover <;> assumption)
