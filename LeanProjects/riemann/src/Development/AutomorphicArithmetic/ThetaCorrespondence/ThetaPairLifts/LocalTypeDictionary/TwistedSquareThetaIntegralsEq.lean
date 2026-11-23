import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelMatchOnOppositeParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguezStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.SquareAgree
theorem twisted_theta_integrals_agree : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  intro hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨-, ⟨c, hc, -⟩, hc0⟩, hCo⟩ := hK' R Rf hR
  obtain ⟨s, hs0, hs⟩ := _root_.GlobalTheory.T.twisted_theta_kernels_agree_up_to_scalar hP.howeDualityReal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
    Pi rf rl p p' hM
  refine ⟨c * s, mul_ne_zero (hc0 c hc) hs0, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ₀, hΦ₀, hrel, Φ₀D, hD₀, hSo⟩ :=
    GlobalTheory.SquareAgree.CoinvPass.coinv_passage D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hTD R Rf hR hCo Φ' hΦ'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  refine ⟨Φ₀, hΦ₀, hrel, GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hTD Φ₀ Φ₀D hD₀
    hconv ?_, fun Φ hΦ hp => ?_⟩
  · obtain ⟨C, k, hC⟩ := hbd 0
    exact ⟨C, k, fun g h => by simpa using hC g h⟩
  · obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
    have hm := hs Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
    funext h
    rw [GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h,
      _root_.Pi.smul_apply,
      GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (kapX X e hO.JX) Φ₀D Φ₀ hO.measW₁ hO.domW₁ (hO.theta_eq_B hD₀) h,
      hc ΦD (s • Φ₀D) hm (kapX X e hO.JX h), I_smul, smul_eq_mul, mul_assoc]
end GlobalTheory.SquareAgree
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_square_theta_integrals_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  first | exact @_root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | exact _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | (intros; apply _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree <;> assumption)
end
