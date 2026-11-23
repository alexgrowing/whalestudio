import Development.WeilBound.CoreStatements.BetaInfinityCoefficients.MatrixCoefficientRankOneSchur
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut

namespace MainStatements.BetaInf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.QuantumDeterminants MeasureTheory Matrix
open scoped InnerProductSpace

theorem betaInfinity_coefficient : Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG.BetaInfCoef := by
  intro hSch k r Wp Wq _ _ _ _ _ _ _ _ Bs ε lam h u u' νq νq' A hG ha ha'
  obtain ⟨hs, -, -, -, hbe, hbe'⟩ := hG
  obtain ⟨hl, hσ, -, -, hw, -, -, -, -, -, -, hHG, -⟩ := hs
  obtain ⟨d, hd, hS⟩ := hSch k r ε lam A.H A.σ Bs.μG hl hσ hHG
  have hw0 : A.w0 ≠ 0 := by
    obtain ⟨_, -, h1, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hdeg : A.deg Bs.μG = d := P.DDSmoothness.fdeg_eq hd hS hw0
  have hDD : A.w0 ∈ DDsp A.σ A.w0 := by
    refine Submodule.subset_span ⟨1, ?_, ?_⟩
    · show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
      simp
    · simp only [(P.MatrixMultiplicationContinuity.sigma_facts hσ).1]
      rfl
  have hc := core Bs hσ A.w0 (A.l A.w0) (A.l' A.w0) ha ha' (A.scal Bs.μG) d (fun v w v' w' => (hS v w v' w').2)
    (hbe _ hDD _ hDD) (hbe' _ hDD _ hDD)
  refine ⟨hc.1, hc.2.trans ?_⟩
  congr 1
  unfold P.CutBP.Jmu.JDat.scal
  rw [hdeg]
  have h1 : ‖A.l A.w0‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have h2 : ‖A.l' A.w0‖ ≠ 0 := norm_ne_zero_iff.2 ha'
  have h3 : d ≠ 0 := hd.ne'
  field_simp

end MainStatements.BetaInf
