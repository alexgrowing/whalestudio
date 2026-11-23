import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformizationPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_uniformization_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left) (U : HolUnif (A ⊗ A) L (g + g)),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → ∀ x₀ : Fin g → ℂ,
    ∃ u' : HolUnif A (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left) g, u'.ex = u.ex ∧
      (∀ j z, (⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull (lift (𝟙 A) (toUnit A ≫ u.ex x₀)).left).U j ↔
        ⊤ ≤ (U.ex (Fin.append z x₀)).left ⁻¹ᵁ L.U (j PUnit.unit))) ∧
      ∀ j z, u'.fr j z = U.fr (j PUnit.unit) (Fin.append z x₀) := by
  first | exact @GlobalTheory.TorusPullFrame.exists_holUnif_pull_right | exact GlobalTheory.TorusPullFrame.exists_holUnif_pull_right | (intros; apply GlobalTheory.TorusPullFrame.exists_holUnif_pull_right <;> assumption)
