import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

abbrev DimX.genericCone {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) : Type :=
  Localization (Algebra.algebraMapSubmonoid (MRing ι ⧸ P) (nonZeroDivisors ℤ))

def DimX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ),
    IsArithVar P (n + 1) →
      ringKrullDim (DimX.genericCone P) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)

theorem DimX.hyps_inhabited : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (1 + 1) :=
  IndefiniteRowSideFullHecke.ArithBezout.isArithVar_projLine'

end GroundTheory.Heights₂.Heights
