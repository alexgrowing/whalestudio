import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactorStatement

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_apply_sum (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    yF X w τ a b = ∑ k, nmat X w τ a k * gsB X w τ k b := by
  simp [yF, yM, Matrix.mul_apply, mat]

theorem gsB_differentiableAt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w => gsB X w τ a b) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hs : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) (fun w hw => hball w hw)
  exact ((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).contDiffAt hs).differentiableAt (by simp)

theorem nmat_differentiableAt (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ a b) 0 :=
  ((PoinPf.diff_nmat X τ a b).restrictScalars ℝ) 0

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    nmat X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  have h := congrFun (congrFun (PoinPf.nmat_zero X τ) a) b
  simpa [mat] using h

theorem gsB_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    gsB X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  rw [gsB_zero]

theorem dY_lower (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ)
    (a b : Fin r) (hba : b < a) : dY X z τ a b = nmat X z τ a b := by
  have hS := (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx).hasFDerivAt
  have h1 := hasFDerivAt_pi'.1 hS τ
  have h2 := hasFDerivAt_pi'.1 h1 a
  have h3 := hasFDerivAt_pi'.1 h2 b
  have hT : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) 0 :=
    HasFDerivAt.fun_sum (fun k _ =>
      (nmat_differentiableAt X τ a k).hasFDerivAt.mul (gsB_differentiableAt X hx τ k b).hasFDerivAt)
  have h3' : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      ((ContinuousLinearMap.proj b).comp ((ContinuousLinearMap.proj a).comp
        ((ContinuousLinearMap.proj τ).comp (dY X)))) 0 := by
    have : (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b) = fun w => yF X w τ a b := by
      funext w; rw [yF_apply_sum]
    rw [this]; exact h3
  have hU := congrArg (fun L => L z) (h3'.unique hT)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hU
  rw [hU]
  have hB0 : (fun w : V (nd X) => gsB X w τ a b) = fun _ => 0 := by
    funext w; exact gsB_lower X w τ hba
  set e := (Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), hba⟩⟩
  have hN : (fun w : V (nd X) => nmat X w τ a b) =
      ⇑((EuclideanSpace.proj e : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext w; simp [nmat, hba, e]; rfl
  have hsum : (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) =
      fderiv ℝ (fun w => gsB X w τ a b) 0 + fderiv ℝ (fun w => nmat X w τ a b) 0 := by
    simp only [nmat_zero_apply, gsB_zero_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum, ContinuousLinearMap.add_apply]
  rw [hB0, hN, fderiv_const_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.zero_apply, zero_add]
  simp [nmat, hba, e] <;> rfl

end GlobalTheory.SUChartSection
