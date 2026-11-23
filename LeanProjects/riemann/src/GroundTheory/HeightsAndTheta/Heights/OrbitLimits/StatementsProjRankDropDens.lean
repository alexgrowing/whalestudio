import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ProjRankDropDens.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (V : Set R.X) (BV : FinHolAtlas n V),
    (∀ j, IsSmoothHerm (L j)) → HoloMap BV R.A Subtype.val →
    ∀ j, ∀ u ∈ (BV.chart j).target, ∀ p : (k : K) → ι k,
      (∀ k, R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0) →
      Module.finrank ℂ (LinearMap.range (fderiv ℂ
        (fun y => ReciprocityTheory.ChartRestriction.G.Geo.affCoord p
          (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm y).1)) u :
          (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) < n →
      locDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val) j u = 0

end GroundTheory.Heights₂.Heights.Targets
