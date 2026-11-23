import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalCombinationOfFixedLocalTranslates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalCombination_of_fixed_localTranslates : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ e f, IsPrimeIdem P e f → ∀ a : GA D V →₀ ℂ, (∀ g ∈ a.support, SuppF V f g) → ∃ c : List ℤ →₀ ℂ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → (∀ k ∈ hyp V P, π k (a.sum fun g z => z • π g u) = a.sum fun g z => z • π g u) → (a.sum fun g z => z • π g u) = opOf π P c u := by
  first | exact @GlobalTheory.SphAvg.fixed_comb_eq_opOf | exact GlobalTheory.SphAvg.fixed_comb_eq_opOf | (intros; apply GlobalTheory.SphAvg.fixed_comb_eq_opOf <;> assumption)
