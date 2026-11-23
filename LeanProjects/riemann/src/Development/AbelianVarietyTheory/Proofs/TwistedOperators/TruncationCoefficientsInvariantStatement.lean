import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationCoefficientsInvariant
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
theorem _root_.GlobalTheory.T.truncation_coefficients_invariant : GlobalTheory.Published.LabesseWaldspurger → ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ Tr, ∃ C Dd : Finset (SV (wittIndex V)) → GA D V → ℂ, (∀ Q ∈ parF (aP P) ∅, Continuous (C Q) ∧ (∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ y, C Q (m * y) = C Q y) ∧ ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ y, C Q (n * y) = C Q y) ∧ (∀ z, Dd ∅ z = 1) ∧ (∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (y * z) : ℂ) = ∑ Q ∈ parF (aP P) ∅, C Q y * Dd Q z) ∧ ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ x, weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr (m * x) = weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x := by
  first | exact @GlobalTheory.weight_split_places | exact GlobalTheory.weight_split_places | (intros; apply GlobalTheory.weight_split_places <;> assumption)
