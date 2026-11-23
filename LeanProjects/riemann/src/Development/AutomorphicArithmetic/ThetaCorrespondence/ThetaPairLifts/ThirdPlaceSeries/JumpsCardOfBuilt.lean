import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem jumpsCard_of_built_alt (hH : HtCard) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (fr : OmFrame b.D) (hp : PhtOn b.A.wd fr fun _ _ _ _ => True) : JumpsCard D'.nd D'.naut := by
  obtain ⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  intro i a r w τ hw hτ hdR
  have hdA := ((Au.wdOf i a r w).2.2.2.1).mp hdR
  have e1 := (Au.wdOf i a r w).2.2.2.2 τ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have e2 := hp.card _ (L.Y.naut.iotaQC i) a r τ w trivial (fun x => (hτ x).symm) hdA
  show Multiset.card (L.Y.jumpsW i r τ) = a
  rw [e1, e2]
theorem jumpsCard_at_members_of_htCard : HtCard → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro hH hL
  refine evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  obtain ⟨fr, -, hp⟩ := (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd).pht
  exact _root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_of_built_alt hH c.a.nt.toNBuilt fr hp
end GlobalTheory.HeightCounting.JumpsAt
end
end
