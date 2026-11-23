import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviLogModulusVector
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_log_modulus_vector : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))), IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ u, vec u ∈ aP P → inner ℝ (vec u) h = - logDelta Φ u m := by
  first | exact @GlobalTheory.LeviVec.exists_levi_vec | exact GlobalTheory.LeviVec.exists_levi_vec | (intros; apply GlobalTheory.LeviVec.exists_levi_vec <;> assumption)
