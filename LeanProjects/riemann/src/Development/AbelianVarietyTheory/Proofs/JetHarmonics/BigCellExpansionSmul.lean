import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem familyDerivativeExpansion_smul (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ)
    (h : Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  obtain ⟨Par, inst, fam, lam, n₁, ninf, c0, q0, Gam, hf, hGam, h1, h2, h3, h4, hstep, hrange, hGb,
    hnorm, hmeas⟩ := h
  refine ⟨Par, inst, fun μ g => t • fam μ g, lam, n₁, ninf, c0, q0, Gam, ?_, hGam, h1, h2, h3, h4, ?_,
    hrange, hGb, ?_, ?_⟩
  · subst hf; rfl
  · intro μ hμ
    obtain ⟨a, hE, hS, hsupp⟩ := hstep μ hμ
    refine ⟨a, ?_, hS, hsupp⟩
    funext c
    have hc := congrFun hE c
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply] at hc ⊢
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam μ) t, smul_comm, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam (μ + ν)) t, smul_comm]
  · intro μ
    rw [Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p (fam μ) t, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p f t]
    gcongr
    exact hnorm μ
  · intro μ
    have e : (fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => t • fam μ g) (P.r + 1) [] (TBB.bigPt P.r c))) =
        fun c => ENNReal.ofReal (‖t‖ ^ 2) *
          ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c)) := by
      funext c
      rw [Formalism.FourierDecayAlt.P.CutBP.Ew_csmul p (fam μ) t, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e]
    exact (hmeas μ).const_mul _

end GlobalTheory
