import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa
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
theorem _root_.GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  first | exact @GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | exact GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | (intros; apply GlobalTheory.FactorSplit.factorIdem_orthSplit_rank <;> assumption)
