import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderBirationalPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

namespace GlobalTheory.BirOrd

theorem ord_and_formOrd_of_over : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), DivOver.Over s E' E →
      (∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (ratPull p s n η) = E.formOrd η := by
  intro X Y _ _ p _ n _ s _ hbij E E' hO
  exact ⟨DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbij E' E hO,
    fun η hη => formOrd_ratPull_of_over ℂ X Y p s hbij E' E hO n η hη⟩

end GlobalTheory.BirOrd
