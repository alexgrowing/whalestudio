import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalScalarPrimeToConjPolarisationLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_scalar_prime_to_conj_polarisationLattice' : ∀ (D : D7) (n : ℕ) (Λ ΛT : Lt D.host.E n), IsAA Λ ΛT → ∀ P : Finset (Formalism.L2.DIV.Pl D.host.E), ∃ γ : D.host.E, γ ≠ 0 ∧ ∃ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) ∧ (∀ v ∈ Λ, ((s : D.host.E) * γ⁻¹) • v ∈ ΛT) ∧ (∀ v ∈ ΛT, ((s : D.host.E) * γ) • v ∈ Λ) := by
  first | exact @GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice | exact GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice | (intros; apply GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice <;> assumption)
