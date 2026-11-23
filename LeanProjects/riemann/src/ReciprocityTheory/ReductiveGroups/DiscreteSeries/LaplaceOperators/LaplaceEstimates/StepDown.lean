import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.MemLpOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapVal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ListProdMemOfForall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SumGammaNnMinus
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2EqZeroOfEqZeroOnUJset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Imports
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsiDatum

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

theorem stepDown : StepDownStatement := by
  intro hIS k r ε u h hsg hp hq lam s hHC hGap hHC' hGap' hu hBNZ
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBd, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hBNZ
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ :=
    LemK.psiDatum (2 * r + k + 1) ε lam h T μ hHC hGap hNeed hq0 hμ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  set y₀ : Mat k r := P * x₀ * P⁻¹ with hy₀
  have hy₀J : y₀ ∈ UJset ε := CurveContinuity.inUJ_conj hP hx₀
  have hy₀inv : y₀⁻¹ = P * (x₀⁻¹ * P⁻¹) := by
    rw [hy₀, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hdet]
  set v : V := ι.symm v₁ with hv
  set w : V := ι.symm v₂ with hw

  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ y₀ ((w : D) : H) ((v : D) : H)) ξ x ≠ 0 := by
    have hcg : ∀ g ∈ UJset ε, coefX σ y₀ ((w : D) : H) ((v : D) : H) g =
        ⟪v₂, S7.PsiM T μ (y₀⁻¹ * g) v₁⟫_ℂ := by
      intro g hg
      have hm : y₀⁻¹ * g ∈ UJset ε := CapelliClosureMembership.inUJ_mul (TDAux.inv_mem hy₀J) hg
      unfold coefX
      rw [hcoef _ hm v w, hv, hw, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [QuotA.per_congr hP hBd _ hcg ξ hx]
    intro h0
    apply hne
    rw [← h0]
    unfold per aaFun
    congr 1
    funext g
    unfold psiCoef
    congr 2
    rw [hy₀inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPP', Matrix.one_mul]
  obtain ⟨β, hβ⟩ := evalM k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp π
    μW μN P hP hBd y₀ w v ξ s x hy₀J hx hu hper

  have hGs : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b m hm => LemK.generated_submodule_stable_under_action V a b hm
  have hvG : (v : D) ∈ genSub E V := LemK.le_generatedSubmodule_dual V v.2
  have hC : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hHC hGap hNeed hq0 _ m hm]
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hxs : Capelli.nnMinus E β (((-(LemK.thV lam s)) : ℝ) : ℂ) (v : D) ∈
      LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s) := by
    have he := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) β β (v : D) hD.glRep hGs hC hvG).2
    have hθ : LemK.thVd lam s = -(LemK.thV lam s) - ((2 * r + k : ℕ) : ℝ) := by
      unfold LemK.thV LemK.thVd
      push_cast
      ring
    rw [hθ]
    exact he
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ :=
    quotM k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp π μW μN P hP hBd
      y₀ w ξ s _ hy₀J hHC' hGap' hxs ⟨x, hx, hβ⟩
  refine finStep hIS k r ε u (lam - Pi.single s 1) h z c Vp π μW μN P hP hBd hp hq hsg hHC' hGap' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y, hy, rfl⟩ := hWf F hF
  have hyG : ∀ c', y c' ∈ genSub E V := (LemK.mem_euler_eigenspace_iff.1 hy).1
  have hspec := tMapD_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) y₀ w
    hy₀J y hyG
  exact ⟨QuotA.contOn_of_smooth hspec.1.1, hspec.2.2 []⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
