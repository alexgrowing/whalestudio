import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRegularDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val → IsClosed V →
    (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    ∀ j, ∀ᵐ u, u ∈ (BV.chart j).target → (BV.chart j).symm u ∉ projRegular R Ψ BV →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0

end GroundTheory.Heights₂.Heights.Targets
