import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.S7

theorem isPsiFor_psiM {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ)
    (hlam : IsHCParam lam) (hμ : IsMu lam μ) (hh : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) (h8 : 8 * (n : ℝ) * q0 ε < h) :
    IsPsiFor ε lam T (PsiM T μ) ∧ ContinuousOn (PsiM T μ) (UJset ε) := by
  refine ⟨⟨fun k₁ k₂ g hg => psiM_equiv T μ k₁ k₂ hg, psiM_one T μ, psiM_smooth T μ hμ,
    fun g hg => psiM_casimir T μ hμ hg, fun ν hν => ?_⟩, psiM_continuousOn T μ hμ⟩
  have := hν
  exact (psiM_integrable T μ hμ hlam hh hq ν).2.1 h8

end ReciprocityTheory.ChartRestriction.DS.S7
