import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothAtBuiltPlace
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefFacts

namespace CompanionTheory.WaveGrid.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity Formalism.QuantumDeterminants MeasureTheory

theorem global_regularity_jacobi : GRegJ :=
  gRegJ_of nilpotent_derivative unitary_capelli_holds group_equations_post_holds smooth_of_coefficients_holds
    (gRegScalar_of group_chart_holds chart_equations_holds classical_to_weak_solution elliptic_regularity_weighted JfS.symbol_nilpotent_holds lie_stabilizer_splitting)

theorem smooth_coefficient_bessel : SmoothKB := by
  intro P Wp Wq _ _ _ _ _ _ p f A hA hCk hCC heig
  have hThr : JF.TransportedAlt P.k P.r A (2 * P.r + P.k + 1) := hA _ (by
    unfold CompanionTheory.JfS.NN
    nlinarith [Nat.zero_le (2 * P.r * (2 * P.r + P.k + 1) * (2 * P.r + P.k + 1))])
  have hF := Gr.jf_mem_FFlM p.T.base A (2 * P.r + P.k + 1) f hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := p.hP
  refine global_regularity_jacobi P.k P.r Wp Wq p.T.base _ _ (B.JF p.T.base f) hTy hTy' hF fun Y => ?_
  obtain ⟨c, hc⟩ := heig Y
  refine ⟨c, fun g hg => ?_⟩
  have hgG : g ∈ B.GV P.k P.r := hg.1
  have hCkn : B.CkOn ((2 * P.r + P.k + 1 : ℕ) : ℕ∞) (B.GV P.k P.r) f := B5.ckOn_mono le_top hCk
  rw [casimir_under_jacquet_integral P.k P.r Wp Wq p.T.base A (2 * P.r + P.k + 1) f (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ q ∂p.T.base.μSS,
      JF.xiP p.T.base q • Q.CV P.k P.r (Y : ℂ) (B.rho p.T.base q f) g =
        c • (JF.xiP p.T.base q • B.rho p.T.base q f g) := by
    filter_upwards [B7.ae_inSS p.T.base] with q hq
    rw [capelli_rho_commute P.k P.r _ _ p.T.base (Y : ℂ) f q hq hCkn _ hgG]
    have hs := B7.sgs_mem p.T.base hq hgG
    simp only [B.rho]
    rw [hc _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end CompanionTheory.WaveGrid.Coef
