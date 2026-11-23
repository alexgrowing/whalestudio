import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.ThetaZeroJetsCurveHolds
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalL

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)

theorem IntOpTwoOrth_of (h : Formalism.L2.Th1.B.ThetaZeroTwoCM) : IntOpTwoOrth := by
  intro d L hd hCM ι W hU hI ha1 ω₀ hω hn1 hn2 n _ κ _ r s N hr hN hodd hs
  obtain ⟨-, -, hG⟩ := h d L hd hCM ι W hU hI ha1 ω₀ hω hn1 hn2
  set R := unitBall ℂ_[2] with hR
  have hmem : ∀ a : ℂ_[2], a ∈ R ↔ ‖a‖ ≤ 1 := fun a => Iff.rfl
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hI
  have hco := Formalism.L2.Th1.A.coeffMem ℂ_[2] W R ((hmem _).2 h1) ((hmem _).2 h2) ((hmem _).2 h3)
    ((hmem _).2 h4) ((hmem _).2 h6)
  have hlog := Formalism.L2.Th1.A.logSpec ℂ_[2] W
  have hexp := Formalism.L2.Th1.A.expSpec ℂ_[2] W
  have hLP : C.IsLogPair (logSer W) (expSer W) :=
    ⟨hlog.1, hlog.2.1, hexp.1, hexp.2.2.2.1, hexp.2.2.1⟩
  have hOU : C.IsOneUnit R (PowerSeries.derivative ℂ_[2] (logSer W)) := by
    rw [hlog.2.2.1]
    refine ⟨?_, hco.2.2.2.2.1⟩
    simp [Formalism.L2.Th1.A.om]
  set T : κ → n → PowerSeries ℂ_[2] :=
    fun k i => E.inW 2 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))) with hT
  have hTI : ∀ k i, E.IntS (T k i) := fun k i => (hG (s k i) N hN hodd (hs k i)).1
  have hInt : DworkPowerSeriesWeights.Integral (E.thetaProd r T) := (E.prodInt ℂ_[2] κ n 0 r T (by simp) hr hTI).2
  have hIM : C.IntMv R (E.thetaProd r T) := fun m => (hmem _).2 (hInt m)
  have hJ := G.jetsIn_toZ hLP hOU hIM
  have heq : G.toZ (expSer W) (E.thetaProd r T) = thetaZ 2 L ι ω₀ r s := by
    rw [KJ.toZ_thetaProd hexp.1]
    unfold thetaZ
    congr 1
    funext k i
    simp only [hT, E.inW]
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlog.1)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hexp.1), hexp.2.2.1, PowerSeries.X_subst]
  rw [heq] at hJ
  have hJI : DworkPowerSeriesWeights.JetsIntegral (thetaZ 2 L ι ω₀ r s) := (G.jets_in_norm_holds ℂ_[2] n _).2 hJ
  refine ⟨hJI, fun P hP => ?_⟩
  show DworkPowerSeriesWeights.jetPair P (thetaZ 2 L ι ω₀ r s) ∈ R
  unfold DworkPowerSeriesWeights.jetPair
  refine Subring.sum_mem _ fun m _ => ?_
  rw [mul_assoc]
  exact Subring.mul_mem _ ((hmem _).2 (hP m)) ((hmem _).2 (hJI m))

theorem integral_operator_two_orthogonal : IntOpTwoOrth := IntOpTwoOrth_of Formalism.L2.Th1.B.th0TwoCM

end Formalism.L2.Th1.Top
