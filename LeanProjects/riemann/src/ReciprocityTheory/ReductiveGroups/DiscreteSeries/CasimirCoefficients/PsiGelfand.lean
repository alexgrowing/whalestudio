import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMExpFormula

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem psiAll : PsiAllStatement n := by
  unfold PsiAllStatement
  intro ε lam h T hHC hgap hq
  obtain ⟨μ, hμ⟩ := exists_mu hHC
  refine ⟨PsiM T μ, fun k₁ k₂ g hg => psiM_equiv T μ k₁ k₂ hg, psiM_one T μ, psiM_smooth T μ hμ,
    fun g hg => psiM_casimir T μ hμ hg, fun k X hX => psiM_dec T μ hμ hHC hgap hq k hX,
    fun ν hν => ?_, fun k g hg => psiM_gelfand T μ hμ k hg, fun μ' hμ' X hX => ?_⟩
  · haveI := hν
    exact psiM_integrable T μ hμ hHC hgap hq ν
  · rw [isMu_unique hμ hμ']
    exact psiM_exp_formula T μ hX

theorem psiExists : PsiExistsStatement n := by
  have hA : PsiAllStatement n := psiAll
  unfold PsiAllStatement at hA
  unfold PsiExistsStatement
  intro ε lam h T hHC hgap hq
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6, -, -⟩ := hA ε lam h T hHC hgap hq
  exact ⟨Ψ, h1, h2, h3, h4, h5, h6⟩

end ReciprocityTheory.ChartRestriction.DS.S7
