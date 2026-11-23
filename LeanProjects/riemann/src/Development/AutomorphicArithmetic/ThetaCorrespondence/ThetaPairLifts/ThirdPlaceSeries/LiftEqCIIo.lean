import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
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
namespace GlobalTheory.Fam.LiftVol
set_option maxHeartbeats 1000000 in
theorem lift_levelP_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ (F : CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1)) (hF : F.1 ∈ (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)), ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q x, liftS ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (F.1 x) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q) = (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) • ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF v hv Q x
  have hio : Lift.IsIo ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j)
      ((_root_.GlobalTheory.Fam.pk_z W).ItY j) ((_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).CC t j) ((_root_.GlobalTheory.Fam.pk_z W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt W hW t j hj
  funext g
  unfold liftS Lift.liftInt
  rw [hsum v hv Q]
  simp_rw [thetaKO_sum_translates]
  have hint : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), IntegrableOn (fun h => (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ hint]
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
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul, Pi.smul_apply, smul_eq_mul]
set_option maxHeartbeats 800000 in
theorem liftS_pt_eq_cI_smul_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j, j + 1 < D.R.m → ∀ (G : (f.t t).CC (j + 1)) P v, liftS ((f.t t).om j) (f.c.vol (j + 1)).μ (f.c.vol (j + 1)).𝓕 (G.1 v) ((f.t t).pt j P) = (f.t t).cI j • ((f.t t).io j G).1 (f.c.It j P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j hj G P v
  have h3 := hP.bot.hyp.2.2.2.1
  have hch : (_root_.GlobalTheory.Fam.pk_z W).IsChain := h3.chain
  have hmod : (_root_.GlobalTheory.Fam.pk_z W).IsModels := h3.models
  obtain ⟨h, hio⟩ := (hR.row t).io j hj G
  have hstep := (hR.row t).vP j hj
  have hk := _root_.GlobalTheory.Fam.LiftVol.lift_levelP_alt W hP t j hj G h
  have hk' := hk _ hstep P v
  have hω := hch.ωY t j hj
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hmod.inf
  have hpt := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j))
    (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (GlobalTheory.VecTheta.isThetaFunO_stepVec hstep) P
  have hvol := hR.meas.vol t j hj
  have hκ := hR.meas.κ (j + 1)
  have hHF : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    by_cases h2 : j + 1 + 1 < D.R.m
    · have h4 := hmod.νY t (j + 1) h2
      exact ⟨h4.1.1, h4.2⟩
    · have h4 := hmod.νY' t
      have e : D.R.m - 1 = j + 1 := by omega
      rw [e] at h4
      exact ⟨h4.1.1, h4.2⟩
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 G.2)
  have hleft : ∀ (w : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))), ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, G.1 w (γ * x) = G.1 w x := by
    intro w γ hγ x
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (hm.aut w).left γ hγ x
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
  have hthL : ∀ g, ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, (_root_.GlobalTheory.Fam.pk_z W).ωY t j (g, γ * x) ((f.t t).pt j P) 0 =
      (_root_.GlobalTheory.Fam.pk_z W).ωY t j (g, x) ((f.t t).pt j P) 0 := by
    intro g γ hγ x
    have e : ((g, γ * x) : GA D (Yc D j) × GA D (Yc D (j + 1))) = (1, γ) * (g, x) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have : IsTopologicalGroup (GA D (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D (Yc D (j + 1))) := ⟨rfl⟩
  have : Countable (GQ (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Yc D (j + 1)).gram
  have hvol' : (f.c.vol (j + 1)).μ = ENNReal.ofReal (f.g.κ (j + 1) * GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j) • (_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) := hvol
  have : (f.c.vol (j + 1)).μ.IsHaarMeasure := (f.c.vol (j + 1)).haar
  have hF₁ := (f.c.vol (j + 1)).fund
  have hF₂ : IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (f.c.vol (j + 1)).μ :=
    hHF.2.mono (by rw [hvol']; exact Measure.smul_absolutelyContinuous)
  funext g
  rw [liftS_apply, hF₁.setIntegral_eq hF₂ (fun γ x => by
    show (_root_.GlobalTheory.Fam.pk_z W).ωY t j (g, (γ : GA D (Yc D (j + 1))) * x) ((f.t t).pt j P) 0 * G.1 v ((γ : GA D (Yc D (j + 1))) * x) = _
    rw [hthL g γ γ.2 x, hleft v γ γ.2 x])]
  rw [hvol', Measure.restrict_smul, integral_smul_measure]
  have hk2 := congrFun hk' g
  rw [liftS_apply] at hk2
  have hv0 : 0 ≤ GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j := by
    unfold GlobalTheory.Fam.volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : 0 ≤ f.g.κ (j + 1) * GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j := mul_nonneg hκ.le hv0
  rw [ENNReal.toReal_ofReal hc0]
  erw [hk2]
  show _ = (cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t j • ((f.row t).io j G).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j P v)) g
  rw [hio]
  simp only [Pi.smul_apply, cIOf, Complex.real_smul, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring
end GlobalTheory.Fam.LiftVol
end
