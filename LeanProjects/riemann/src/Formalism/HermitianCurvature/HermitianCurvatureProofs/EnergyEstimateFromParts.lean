import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedL2ConstMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cauchy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov

namespace Formalism.FourierDecayAlt.P

theorem le_thetaForm_proof : Formalism.FourierDecayAlt.LE.ThetaForm := by
  intro ε σ hε v
  simp only [LE.th]
  have hv := Real.exp_pos v
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]
    field_simp
    try ring
  rw [h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

theorem le_thetaRange_proof : Formalism.FourierDecayAlt.LE.ThetaRange := by
  intro ε σ x hε hσ hx
  simp only [LE.th]
  have hb : 0 < x / (x + ε) := by positivity
  exact ⟨Real.rpow_pos_of_pos hb σ, Real.rpow_le_one hb.le ((div_le_one (by linarith)).mpr (by linarith)) hσ⟩

theorem le_thetaSmooth_proof : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.LEx1.thetaSmooth

theorem le_thetaBound_proof : Formalism.FourierDecayAlt.LE.ThetaBound := Formalism.FourierDecayAlt.P.LEx1.thetaBound

theorem theta_limit : Formalism.FourierDecayAlt.LE.ThetaLimit := Formalism.FourierDecayAlt.P.LEx1.thetaLimit

theorem le_thetaMono_proof : Formalism.FourierDecayAlt.LE.ThetaMono := by
  intro σ ε ε' x hσ hε hεε' hx
  simp only [LE.th]
  have hε' : 0 < ε' := by linarith
  have hb : 0 < x / (x + ε') := by positivity
  exact Real.rpow_le_rpow hb.le (by gcongr) hσ

theorem cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.LEx1.cutBound

theorem cutoff_theta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.LEx1.cutTheta

theorem leibniz_rule : Formalism.FourierDecayAlt.LE.Leibniz := Formalism.FourierDecayAlt.P.LEx1.leibniz

theorem le_termZero_proof : Formalism.FourierDecayAlt.LE.TermZero := Formalism.FourierDecayAlt.P.LEx1.termZero

theorem measure_measurable : Formalism.FourierDecayAlt.LE.DsMeas := Formalism.FourierDecayAlt.P.LEx1.dsMeas

theorem coefficient_integrable : Formalism.FourierDecayAlt.LE.CoefIntegrable := Formalism.FourierDecayAlt.P.LEx1.coefIntegrable

theorem adjoint_identity : Formalism.FourierDecayAlt.LE.Adj := Formalism.FourierDecayAlt.P.LEx1.adj

theorem energy_finite : Formalism.FourierDecayAlt.LE.EFinite := Formalism.FourierDecayAlt.P.LEx1.eFinite

theorem cauchy_schwarz_term : Formalism.FourierDecayAlt.LE.CSTerm := Formalism.FourierDecayAlt.P.LEx1.csTerm

theorem le_shiftBound_proof : Formalism.FourierDecayAlt.LE.ShiftBound := Formalism.FourierDecayAlt.P.LEx1.shiftBound

theorem markov_term : Formalism.FourierDecayAlt.LE.MarkovTerm := Formalism.FourierDecayAlt.P.LEx1.markovTerm

theorem le_termBound_proof : Formalism.FourierDecayAlt.LE.TermBound := Formalism.FourierDecayAlt.P.LEx1.termBound

theorem geometric_sum_bound : Formalism.FourierDecayAlt.LE.GeomSum := by
  intro c x R hc hx hx1
  have ha0 : 0 ≤ Real.exp 1 * √c := by positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √c) := by positivity
  have hx1' : x * (2 * (1 + 2 * Real.exp 1 * √c)) ≤ 1 := by
    rw [le_div_iff₀ hden] at hx1
    exact hx1
  have hxlt : x < 1 := by nlinarith [mul_nonneg ha0 hx]
  have hgeom : ∑ p ∈ Finset.Icc 1 R, x ^ p ≤ x / (1 - x) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := R + 1) hx hxlt
    rw [pow_one] at h
    have hI : Finset.Ico 1 (R + 1) = Finset.Icc 1 R := by
      ext p
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rwa [hI] at h
  have h2 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg ha0 hx]
  rw [← Finset.mul_sum]
  calc Real.exp 1 * √c * ∑ p ∈ Finset.Icc 1 R, x ^ p ≤ Real.exp 1 * √c * (2 * x) :=
        mul_le_mul_of_nonneg_left (hgeom.trans h2) ha0
    _ ≤ 1 / 2 := by nlinarith [mul_nonneg ha0 hx]

theorem energy_estimate : Formalism.FourierDecayAlt.LE.EnergyStep := Formalism.FourierDecayAlt.P.LEx1.energyStep

theorem absorb_term : Formalism.FourierDecayAlt.LE.Absorb := Formalism.FourierDecayAlt.P.LEx1.absorb

theorem le_uniformBound_proof : Formalism.FourierDecayAlt.LE.UniformBound := Formalism.FourierDecayAlt.P.LEx1.uniformBound

theorem fatou_estimate : Formalism.FourierDecayAlt.LE.FatouStep := Formalism.FourierDecayAlt.P.LEx1.fatouStep

theorem dominated_convergence : Formalism.FourierDecayAlt.LE.DomConv := Formalism.FourierDecayAlt.P.LEx1.domConv

theorem energy_estimate_from_parts : Formalism.FourierDecayAlt.LE.StepClaimFromSteps := Formalism.FourierDecayAlt.P.LEx1.stepClaimFromSteps_full

theorem energy_estimate_of_lemmas : Formalism.FourierDecayAlt.LE.StepClaim :=
  Formalism.FourierDecayAlt.P.LEx1.stepClaimFromSteps_full Formalism.FourierDecayAlt.P.cauchy_theta_identity Formalism.FourierDecayAlt.P.markov_inequality_vector
    Formalism.FourierDecayAlt.P.LEx1.thetaForm Formalism.FourierDecayAlt.P.LEx1.thetaRange Formalism.FourierDecayAlt.P.LEx1.thetaSmooth Formalism.FourierDecayAlt.P.LEx1.thetaBound
    Formalism.FourierDecayAlt.P.LEx1.thetaLimit Formalism.FourierDecayAlt.P.LEx1.cutTheta Formalism.FourierDecayAlt.P.LEx1.leibniz Formalism.FourierDecayAlt.P.LEx1.termZero
    Formalism.FourierDecayAlt.P.LEx1.coefIntegrable Formalism.FourierDecayAlt.P.LEx1.adj Formalism.FourierDecayAlt.P.LEx1.eFinite Formalism.FourierDecayAlt.P.LEx1.csTerm
    Formalism.FourierDecayAlt.P.LEx1.shiftBound Formalism.FourierDecayAlt.P.LEx1.markovTerm Formalism.FourierDecayAlt.P.LEx1.termBound Formalism.FourierDecayAlt.P.LEx1.geomSum
    Formalism.FourierDecayAlt.P.LEx1.energyStep Formalism.FourierDecayAlt.P.LEx1.absorb Formalism.FourierDecayAlt.P.LEx1.uniformBound Formalism.FourierDecayAlt.P.LEx1.fatouStep
    Formalism.FourierDecayAlt.P.LEx1.domConv

end Formalism.FourierDecayAlt.P
