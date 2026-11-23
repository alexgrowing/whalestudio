import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V V' : X.Opens, IsAffineOpen V → V ≤ V' → (∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) → V' = V := by
  first | exact @GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | exact GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | (intros; apply GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one <;> assumption)
