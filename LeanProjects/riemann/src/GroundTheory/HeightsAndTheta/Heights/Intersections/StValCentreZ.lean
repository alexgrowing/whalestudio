import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocIntegral
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def IsValCentre {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) [P.IsPrime]
    (R : ValuationSubring (FractionRing (MRing ι ⧸ P))) (y : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime y ∧ P ≤ y ∧
    ∀ (b : K → ℕ) (f g : MRing ι), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) ∈ R.nonunits)

def ValCentreZ.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (hP : IsMultiProjPrime P),
    haveI := hP.1
    ∀ R : ValuationSubring (FractionRing (MRing ι ⧸ P)), ∃ y : Ideal (MRing ι), IsValCentre P R y

end GroundTheory.Heights₂.Heights.Inter
