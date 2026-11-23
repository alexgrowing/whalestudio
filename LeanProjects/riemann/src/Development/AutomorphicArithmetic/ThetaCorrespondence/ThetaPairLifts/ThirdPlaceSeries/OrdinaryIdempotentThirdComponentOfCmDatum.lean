import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadThirdLocalOfCoeffStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Up.ThirdTied
theorem ordinary_idempotent_third_component_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m _ _ s r _ hC Xd E labPi hb htup hg hf
  exact GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ m.intersectionNumber_baseChange.ok.ok2
end GlobalTheory.HeightCounting.Up.ThirdTied
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_idempotent_third_component_of_cmDatum_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt | exact _root_.GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt <;> assumption)
end
end
