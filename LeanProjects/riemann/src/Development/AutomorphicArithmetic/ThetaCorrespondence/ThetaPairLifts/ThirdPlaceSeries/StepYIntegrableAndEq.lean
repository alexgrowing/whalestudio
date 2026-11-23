import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FockVecEqSumStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoLevChiStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BaseChain.stepY_integrable_and_eq_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (t) (j) (hj : j + 1 < D.R.m) (F : CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1)) (hF : F.1 ∈ (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)) (v) (hv : IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v) (Q x g) :
  IntegrableOn (fun h => thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g h (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q) * F.1 x h) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ∧
  (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1), thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q) * F.1 x y ∂((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1))) = (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) g := by
  have hio : Lift.IsIo ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j)
      ((_root_.GlobalTheory.Fam.pk_z W).ItY j) ((_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).CC t j) ((_root_.GlobalTheory.Fam.pk_z W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.T.exists_level_elements_step_vector_alt W hW t j hj
  rw [hsum v hv Q]
  simp_rw [GlobalTheory.BaseChain.thetaKO_sum_smul_act]
  have hint : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), IntegrableOn (fun h => (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  refine ⟨integrable_finset_sum _ hint, ?_⟩
  rw [integral_finset_sum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), ∫ h in (_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1), (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h ∂(_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) =
      ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, _root_.GlobalTheory.T.chain_projection_level_character_alt W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul]
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BaseChain.stepY_isIo_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hrow := hf.row W.P.A3.A.μ0
  have hfin : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  have hc : Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H ≠ 0 := Nat.card_pos.ne'
  have hne : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hc)
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have hI := (_root_.GlobalTheory.BaseChain.stepY_integrable_and_eq_alt W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).1.smul_measure hne
    rw [← Measure.restrict_smul] at hI
    exact hI
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have e := (_root_.GlobalTheory.BaseChain.stepY_integrable_and_eq_alt W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).2
    have hk : (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) = 1 := by
      rw [Complex.real_smul, _root_.GlobalTheory.BaseChain.inverseLevelCardinality, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hc)]
    show (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 (j + 1), thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((f.row W.P.A3.A.μ0).vP j) φ) * F.1 v y ∂(_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 (j + 1))) = ((f.row W.P.A3.A.μ0).io j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ v) g
    rw [hio, Measure.restrict_smul, integral_smul_measure]
    exact (congrArg (fun z => (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • z) e).trans (by rw [← smul_mul_assoc, hk, one_mul])
end
