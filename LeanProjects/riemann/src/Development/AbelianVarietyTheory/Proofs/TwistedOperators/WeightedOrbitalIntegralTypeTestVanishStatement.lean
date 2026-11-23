import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
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
theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ v : T.S, (μf v).IsHaarMeasure → ∀ (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), IsRegSS γ.1.1 → ε * ε = ε → γ.1.1 * ε = ε * γ.1.1 → 0 < ε.rank → ε.rank < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank ε.rank) → ∀ b : GLoc D.sp.cm.sig V.gram v → ℂ, Continuous b → LeftInv (cent (proj D.sp.cm.sig V.gram v (rat V γ))) b → (∀ g, ε.map (T.frame v).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1) * (1 - ε.map (T.frame v).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1 → ∀ x, b (g * x) = b x) → ∀ (dt : Measure (cent (proj D.sp.cm.sig V.gram v (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (proj D.sp.cm.sig V.gram v (rat V γ))) dt (μf v) (fun x => b x * ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x)) 0 := by
  first | exact @GlobalTheory.TwistLocal.weighted_orbital_vanish | exact GlobalTheory.TwistLocal.weighted_orbital_vanish | (intros; apply GlobalTheory.TwistLocal.weighted_orbital_vanish <;> assumption)
