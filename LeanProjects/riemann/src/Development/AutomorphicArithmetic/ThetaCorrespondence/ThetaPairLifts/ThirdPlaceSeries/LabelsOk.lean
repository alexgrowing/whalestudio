import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameLab
variable {D : D7}
theorem labels_ok_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ Q
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam (p.R.mu w) Q.1 Q.2
  refine ⟨⟨plOf p j (p.R.mu w) Q, fun e => h2 e.symm, (under_conjPl _).symm⟩, under_conjPl _,
    (absNorm_conjPl _).trans h3.symm, mem_conjPl_of_fixed _ (map_natCast _ _)⟩
end GlobalTheory.FrameLab
end
