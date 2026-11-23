import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedKernelOrbitSum
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
theorem _root_.GlobalTheory.T.truncated_kernel_orbit_sum : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (K : Subgroup (GA D V)) (f : GA D V → ℂ), (∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f) → ∀ 𝔬 : Set (GF V), (∀ δ ∈ 𝔬, ∀ g, g * δ * g⁻¹ ∈ 𝔬) → ∀ Tr x, kT Φ K 𝔬 f Tr x = ∑' δ : 𝔬, f (x⁻¹ * rat V δ * x) := by
  first | exact @GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish | exact GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish | (intros; apply GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish <;> assumption)
