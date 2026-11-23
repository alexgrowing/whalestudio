import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyPlaceAdditive
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_family_place_additive : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → (∀ Tr, Continuous fun x => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q) ∧ ∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, ∀ Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr Q = (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 Q - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0 Q) + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q := by
  first | exact @GlobalTheory.TruncKer.yfam_continuous_add | exact GlobalTheory.TruncKer.yfam_continuous_add | (intros; apply GlobalTheory.TruncKer.yfam_continuous_add <;> assumption)
