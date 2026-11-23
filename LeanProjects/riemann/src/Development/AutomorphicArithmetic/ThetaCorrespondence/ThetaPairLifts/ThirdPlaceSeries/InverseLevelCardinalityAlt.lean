import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastStepIntegrableOnStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelPStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
theorem stepX_isIo_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceX W).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hf j h
  have hcard : Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H ≠ 0 := by
    have hf' : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    exact Nat.card_pos.ne'
  have hcH : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := by
    simp [_root_.GlobalTheory.BaseChain.inverseLevelCardinality]
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · have h1 := _root_.GlobalTheory.T.top_step_vector_property_alt W hP j h _ ((hf.row W.P.A3.A.μ0).vT j h) F φ v g
    unfold IntegrableOn at h1 ⊢
    change Integrable _ ((_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0).restrict ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0))
    rw [Measure.restrict_smul]
    exact h1.smul_measure hcH
  · obtain ⟨h', -, hL⟩ := _root_.GlobalTheory.T.extra_column_range_membership_alt W u hP f.g W.P.A3.A.μ0 j h F
    obtain ⟨h'', he⟩ := (hf.row W.P.A3.A.μ0).ioT j h F
    have e1 := congrFun (hL _ ((hf.row W.P.A3.A.μ0).vT j h) φ v) g
    have key : ∀ X : ℂ, (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * X) = X := by
      intro X
      have e3 : (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal = ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℝ))⁻¹ := by
        simp [_root_.GlobalTheory.BaseChain.inverseLevelCardinality, ENNReal.toReal_inv]
      have hc : ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcard
      rw [e3, Complex.real_smul, ← mul_assoc]
      push_cast
      rw [inv_mul_cancel₀ hc, one_mul]
    change ∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0, _ ∂(_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) =
      ((f.row W.P.A3.A.μ0).ioT j h F).1 (f.c.ItT j h φ v) g
    rw [setIntegral_smul_measure_complex, he]
    have e2 : (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0, thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
          (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row W.P.A3.A.μ0).vT j h) φ) * F.1 v y ∂(_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) =
        (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * (ioXT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h ⟨F.1, h''⟩).1 (f.c.ItT j h φ v) g := e1
    exact (congrArg (fun z : ℂ => (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • z) e2).trans (key _)
end GlobalTheory.BaseChain
end
end
