import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestDataTraceIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_data_trace_identity : ∀ {D : D7} {V : HSp D}, GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ {lam : D.what₂.Tau → Fin V.rank → ℤ} {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}, IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : WittFrame V) (K : Subgroup (GA D V)) (γ : GF V) (Tr : A0 (wittIndex V)) (x : GA D V), kT Φ K {δ | IsConj γ δ} (tensor D.sp.cm.sig V.gram fa ff) Tr x = classKernel (GQ V) (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x := by
  first | exact @GlobalTheory.KTClass.kT_eq_classKernel | exact GlobalTheory.KTClass.kT_eq_classKernel | (intros; apply GlobalTheory.KTClass.kT_eq_classKernel <;> assumption)
