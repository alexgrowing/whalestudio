import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelElementsStepVector
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

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FockVecSum
theorem fockVec_eq_sum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H], ∃ κ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q, pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ • ((_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ p, 1)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj _
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hj' : j < D.R.m := Nat.lt_of_succ_lt hj
  have hlift := GlobalTheory.ChainEquiv.lifts_chain (_root_.GlobalTheory.Fam.pk_z W).toLevCh W.P.A3.A.μ0 hL t j hj'
  choose κ hκ using fun p : (_root_.GlobalTheory.Fam.complexLevelStructure W).H => hlift p.1
  refine ⟨κ, fun p => ⟨(hκ p).1, (hκ p).2.1, (hκ p).2.2 ▸ p.2⟩, fun v hv Q => ?_⟩
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hL t ⟨j, hj'⟩
  obtain ⟨c, hc⟩ := hL.βY j hj'
  obtain ⟨c', hc'⟩ := hL.βY (j + 1) hj
  have hω := hC.chain.ωY t j hj
  have hvY := hC.chain.vY t j hj
  have hsum := GlobalTheory.StepVecSum.stepVec_eq_sum D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) ((_root_.GlobalTheory.Fam.pk_z W).vY t j) v hω
    (D.sp.Y_sig _) (D.sp.Y_sig _) (GlobalTheory.Chain.VacVec.cart_isCartanInv ((_root_.GlobalTheory.Fam.pk_z W).MY j))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hj'))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (j + 1) hj)) hc.1 hc'.1 D.R.r D.R.t j (r_le_Y j)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D _ _ _ hL t).1 (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) (_root_.GlobalTheory.Fam.complexLevelStructure W) hvY hv
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hvY.1.2.inf
  have hf : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vY t j) := by
    have := hC.chain.ptY t j hj 1
    rwa [RealDat.ptY, GlobalTheory.FiniteFock.pureTensorO_one] at this
  rw [hsum, GlobalTheory.SpecFac.pureTensorO_sum hω.std hθ _ _ _ _ Finset.univ _ _ (fun p _ => hω.om_pres _ _ hf)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hk := GlobalTheory.FiniteFock.compAt_mt_of_finite (_root_.GlobalTheory.Fam.pk_z W).θ
  refine ((GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hω hθ _ _ _ _ _ _ _ _ (κ p) 1
    (fun τ => by rw [hk τ (hκ p).1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (hκ p).1, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.one_mul]) _ hf Q).2).symm
end GlobalTheory.FockVecSum
end
