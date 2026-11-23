import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

def YmDeriv : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) (γ α : Fin (WeightFamilies.dimY D j) → ℕ),
    (∑ i, γ i) ≤ ∑ i, α i →
      hasse X la G.w (bcol jj α) ((ym G la γ : ↥(Frac0 X la G.w)) : Lw X la G.w) =
        if γ = α then ((wfr G la jj : ↥(Frac0 X la G.w)) : Lw X la G.w) ^ (∑ i, α i) else 0

end PoleLengthBounds
