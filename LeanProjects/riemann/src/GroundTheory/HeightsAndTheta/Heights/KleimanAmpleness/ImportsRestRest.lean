import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def RealiseRestrict.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
        IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀ → mIdealOver F y ≤ mIdealOver F y' →
        ∀ hxy : (∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0),
          ∃ (Q' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm)) (r : Ω → K'),
            Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ BundleRealises y' k₀ Q' β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
