import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTestVanishing
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
theorem _root_.GlobalTheory.T.regular_semisimple_test_vanishing : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → (∀ v, (μf v).IsHaarMeasure) → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (Φ : WittFrame V) (u : SV (wittIndex V)) (γ : GF V), u ≠ 0 → IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → ∀ C : GA D V → ℂ, Continuous C → LeftInv (cent (rat V γ)) C → (∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C) → ∀ (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure] (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) * ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  first | exact @GlobalTheory.TypesFactor.typesFactor_vanish | exact GlobalTheory.TypesFactor.typesFactor_vanish | (intros; apply GlobalTheory.TypesFactor.typesFactor_vanish <;> assumption)
