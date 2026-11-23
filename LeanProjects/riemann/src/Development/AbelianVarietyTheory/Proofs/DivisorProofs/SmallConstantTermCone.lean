import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinAtMinusRhoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenIntegralStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenIntegralHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenIntegralMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmall

theorem ctSmallCone : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTSmallCone := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hc e' he' K μK μ hK hμK hμ
  obtain ⟨C, hC, h3⟩ := GlobalTheory.T.config_b_eigen_integral_measure hP (GlobalTheory.T.eisenstein_at_minus_rho hP) F E σ B a b G G₁ H H' hc e' he' K μK μ hK hμK hμ
  refine ⟨C, hC, fun X om om' om₁ om₁' hT hT₁ Φ' hΦ' fa fb hsp h₁ m hm h => ?_⟩
  obtain ⟨fa', hla, hct⟩ := h3 X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  have hlb := GlobalTheory.T.config_b_eigen_integral_haar hP F E σ B a b G G₁ H H' hc e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'.2
  have hsp' : Split2 G₁.W H' X (G.M'.I om' Φ') fa'
      (fun h => C * coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (((a - (b + 2)) / 2 + 1 : ℕ) : ℂ) h) := by
    refine ⟨hct, hla, fun t m' hm' h' => ?_⟩
    simp only
    rw [hlb t m' hm' h']
    ring
  obtain ⟨x, -, hx⟩ := (GlobalTheory.T.split_existence hP F E σ B a (b + 2) G X om om' hT (a + b) G₁.W H' a (a + b + 1) hc.hH').2 Φ' hΦ'
  have e1 := hx (fa, fb) hsp
  have e2 := hx (fa', fun h => C * coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (((a - (b + 2)) / 2 + 1 : ℕ) : ℂ) h) hsp'
  have hfb : fb = _ := congrArg Prod.snd (e1.trans e2.symm)
  rw [hfb]
  simp only
  rw [GlobalTheory.T.config_b_eigen_integral_stabilizer hP F E σ B a b G G₁ H H' hc e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h₁ m hm h]

end GlobalTheory.ConeSmall

end
