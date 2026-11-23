import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
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
theorem _root_.GlobalTheory.T.regular_centralizer_noncompact : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, (μa w).IsHaarMeasure) → IsTestArchG M μa fa → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ γ : GF V, IsRegSS γ.1.1 → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w)) → ∀ b : GA D V → ℂ, Continuous b → LeftInv (cent (rat V γ)) b → (∀ g x, b (embArch D.sp.cm.sig V.gram w g * x) = b x) → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], HasQuotInt (cent (rat V γ)) dt μ (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x) 0 := by
  first | exact @GlobalTheory.ArchVanish.hasQuotInt_weighted_eq_zero | exact GlobalTheory.ArchVanish.hasQuotInt_weighted_eq_zero | (intros; apply GlobalTheory.ArchVanish.hasQuotInt_weighted_eq_zero <;> assumption)
