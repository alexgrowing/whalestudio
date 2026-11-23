import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolutionDivisorsTopFormNormalCrossings
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_resolution_divisors_topForm_normalCrossings : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n)
    (G D₀ : CartierDiv X), η ≠ 0 →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s)
      (B : Closeds Y),
      SmoothOfRelativeDimension n (s ≫ p) ∧ IsProper s ∧ Function.Bijective (functionFieldMap s) ∧
      {v : Y | v ∈ B ∧ Order.coheight v = 1}.Finite ∧ ratPull p s n η ≠ 0 ∧
      (∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
        (u : Fin n → Y.functionFieldˣ), IsSncChart (s ≫ p) n B y U hy z J w u) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → G.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (y v : Y) (g : X.functionFieldˣ), v ⤳ y → Order.coheight v = 1 → v ∉ B → D₀.IsEqn (s y) g →
        Scheme.ord (fnPull s g : Y.functionField) v = 0) ∧
      (∀ (v : Y) (F : DivOver (s ≫ p)), Order.coheight v = 1 → v ∉ B → F.IsAt v →
        F.formOrd (ratPull p s n η) = 0) := by
  first | exact @GlobalTheory.ResPairSupp.exists_resolution_supp | exact GlobalTheory.ResPairSupp.exists_resolution_supp | (intros; apply GlobalTheory.ResPairSupp.exists_resolution_supp <;> assumption)
