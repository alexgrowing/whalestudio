import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTriangleTransfer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralsAgreeOfIntegrableKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFiniteDataMatchEachStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTriangleTransferStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct
theorem GlobalTheory.StageLift.theta_stage_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank), (∀ t, lam t ≠ 0) ∧
        ∀ t P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') → X.I W.ψ W.θ t (s P') = lam t • X.I' W.ψ W.θ t P' := by
  intro hP hK hL
  have hM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hL
  have hWe := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hL
  have hAg := _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_tripleConditions (_root_.GlobalTheory.T.theta_finiteData_match_each_stage hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL' G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨h1, h3⟩ := h C hC D large₂ a b r T Lc μ hL' G
  obtain ⟨FA, FA', FW, ea, eb, hd⟩ := h1 W i j p q A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, qm, qm', hq, hq', hLM⟩ := hM D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨g, hg⟩ := qm.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have key : ∀ t, ∃ l : ℂ, l ≠ 0 ∧ ∀ P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      X.I W.ψ W.θ t (g (qm' P')) = l • X.I' W.ψ W.θ t P' := by
    intro t
    obtain ⟨hT, hE, hf, hf', hk, hk'⟩ := hd t
    obtain ⟨hex, hall⟩ := hLM _ _ hT hE
    obtain ⟨Pim, rf, rl, pm, pm', hm⟩ := hWe D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hT hex (X.ω t) (X.ω' t)
      (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hall _ _ _ _ _ _ _ hm
    obtain ⟨κ, hκ, hrk⟩ := h3 W i j p q A A' WW X hX FA FA' FW t hf hf' Pim rf rl pm pm' hm Pr Pf qm qm' r r' e hq hq' hr hr'
    obtain ⟨c, hc0, hcI⟩ := hAg D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hT X.m X.fd X.m' X.fd' hIs.meas hIs.meas' _ _ _ _ _ _ _ hm
    refine ⟨c * κ, mul_ne_zero hc0 hκ, fun P' hP' => ?_⟩
    have hΦ : GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) (g (qm' P')) ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW :=
      Submodule.subset_span ⟨X.f t, g (qm' P'), hf, rfl⟩
    have hΦ0 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
      Submodule.subset_span ⟨X.f' t, P', hf', rfl⟩
    have hΦ' := Submodule.smul_mem _ κ hΦ0
    have hsm : ∀ x h, thetaKO (X.ω' t) x h (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') =
        κ * X.ker' W.ψ W.θ t P' h x := by
      intro x h
      rw [← hk' P' x h]
      simp [thetaKO, map_smul]
    have hint : ∀ h, MeasureTheory.IntegrableOn
        (fun x => thetaKO (X.ω' t) x h (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P')) X.fd' X.m' := by
      intro h
      simp_rw [hsm]
      exact (hP' h).const_mul κ
    have hqg : qm (g (qm' P')) = qm' P' := LinearMap.congr_fun hg _
    have hp : pm (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) (g (qm' P'))) =
        pm' (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
      rw [hr _ hf, map_smul, hr' _ hf', hqg, hrk, TensorProduct.tmul_smul, map_smul]
    have h1 := hcI _ hΦ _ hΦ' hint hp
    funext h
    have h2 := congrFun h1 h
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Tri.I, Tri.I', Pi.smul_apply, smul_eq_mul]
    simp_rw [← hk]
    rw [h2]
    simp_rw [hsm]
    rw [MeasureTheory.integral_const_mul]
    ring
  choose lam hlam using key
  exact ⟨lam, g ∘ₗ qm', fun t => (hlam t).1, fun t P' hP' => (hlam t).2 P' hP'⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stage_liftable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank), (∀ t, lam t ≠ 0) ∧
        ∀ t P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') → X.I W.ψ W.θ t (s P') = lam t • X.I' W.ψ W.θ t P' := by
  first | exact @_root_.GlobalTheory.StageLift.theta_stage_lift_exists | exact _root_.GlobalTheory.StageLift.theta_stage_lift_exists | (intros; apply _root_.GlobalTheory.StageLift.theta_stage_lift_exists <;> assumption)
end
