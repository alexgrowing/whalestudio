import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModel
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_trace_from_model : GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : GlobalTheory.TruncKer.WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ γ : GlobalTheory.TruncKer.GF V, IsRegSS γ.1.1 → ∀ P, GlobalTheory.TruncKer.IsMinLevi Φ γ P → P ≠ ∅ → ∀ (dt : Measure (cent (GlobalTheory.TruncKer.rat V γ))) [dt.IsHaarMeasure] (Tr : _), wOrbInt (cent (GlobalTheory.TruncKer.rat V γ)) dt μ (GlobalTheory.TruncKer.rat V γ) (fun x => GlobalTheory.TruncKer.weight Φ (levelAll D.sp.cm.sig V.gram L a) (GlobalTheory.Chamber.aP P) Tr x) (tensor D.sp.cm.sig V.gram fa ff) = 0 := by
  first | exact @GlobalTheory.LeviOrb.wOrbInt_eq_zero | exact GlobalTheory.LeviOrb.wOrbInt_eq_zero | (intros; apply GlobalTheory.LeviOrb.wOrbInt_eq_zero <;> assumption)
