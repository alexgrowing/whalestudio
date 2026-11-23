import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SecsTwistSysPtX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def NumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n →
          Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun i => (L i).toSubSystem) =
            NumbersDVR.intNum F (mIdealOver F y) δ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
