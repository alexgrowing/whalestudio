import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldChartRingOverPnPtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver cellMon locPart quotPart)

def CechPointEval.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c)) →
    ∀ β : K → ℤ, ∃ (V : Submodule F Ω)
      (φ : ∀ I : ∀ k, Finset (ι k),
        LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y) →ₗ[F] Ω),
      ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0) →
        (∀ (g : MRingOver F ι) (t : cellMon F I),
          φ I (LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver F y) g) t) =
            aeval y g / aeval y (t : MRingOver F ι)) ∧
        Set.InjOn (φ I) (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β) ∧
        (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β).map (φ I) = V

example (F : Type) [Field F] (h : CechPointEval.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0)
    (fun c _ => isField_chartRingOver_pnPt_zero F c) 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
