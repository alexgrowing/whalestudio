import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStageYValid
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QBaseEmpty

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem under_mem_S_alt {W : _root_.GlobalTheory.MiS.RealPackAlt ex} (hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (_root_.GlobalTheory.BaseChain.com_z W).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D (_root_.GlobalTheory.Fam.pk_z W).C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, (hL.Pg P).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨P', (hL.Pg P').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]
theorem stage_y_is (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (j : ℕ) (hj : j < D.R.m) :
    (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Is (_root_.GlobalTheory.BaseChain.com_z W) j := by
  have hC := hP.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hM : (_root_.GlobalTheory.Fam.pk_z W).IsModels := hC.models
  have hQ := _root_.GlobalTheory.BaseChain.Q_base_eq_empty W
  have hm : min j D.R.m = j := min_eq_left hj.le
  obtain ⟨c, hc⟩ := hL.βY j hj
  have hν : ((_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) ((_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j) := by
    by_cases h1 : j + 1 < D.R.m
    · exact ⟨(hM.νY _ j h1).1.1, (hM.νY _ j h1).2⟩
    · have : j = D.R.m - 1 := by omega
      subst this
      exact ⟨(hM.νY' _).1.1, (hM.νY' _).2⟩
  haveI := hν.1
  refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [D.sp.Y_rank _ (min_le_right _ _), hm]
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [D.Y_sigval _ (min_le_right _ _), hm]
  · show parB _ (min j D.R.m) = _
    rw [hm]
  · push_cast at hN
    have := P.isPrime.mem_of_pow_mem _ hN
    rcases P.isPrime.mem_or_mem this with h0 | h0
    · exact _root_.GlobalTheory.BaseChain.under_mem_S_alt hL 0 P h0
    · exact _root_.GlobalTheory.BaseChain.under_mem_S_alt hL 1 P h0
  · show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [hQ]; rfl
  · exact (MeasureTheory.Measure.IsHaarMeasure.smul _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W) :
      (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j).IsHaarMeasure)
  · exact hν.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)
end GlobalTheory.BaseChain
end
end
