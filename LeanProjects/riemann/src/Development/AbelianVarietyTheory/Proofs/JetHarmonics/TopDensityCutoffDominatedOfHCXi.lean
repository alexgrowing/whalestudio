import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePowerStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem topDensity_cut_dominated_all :
    GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  intro hΞ Cb
  obtain ⟨Cc, H⟩ := GlobalTheory.HatNF.top_density_dominated hΞ (fun _ => 0) GlobalTheory.T.basicOperators_polynomialLift_no_inversePower Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  obtain ⟨hm, h, hi, hb⟩ := H Wp Wq P p f A₀ p₀ χ N w a1 a2 a3 a4 a5 (by simpa using a6) hw.1 hN
  have e : ∀ ε : ℝ,
      D.cutF p.T.base χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f := by
    intro ε
    funext g
    simp only [D.cutF, Formalism.FourierDecayAlt.P.TBBx4.fpm, mulG, ContinuousLinearMap.comp_id, smul_smul]
    try push_cast
    try rfl
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε => ?_, h, hi,
    eventually_nhdsWithin_of_forall fun ε hε => ae_of_all _ fun c => ?_⟩
  · rw [e]; exact hm ε hε
  · rw [e]; exact hb ε hε c
end GlobalTheory.HatNF
