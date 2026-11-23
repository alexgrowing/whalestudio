import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLattic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceModPrime_of_polarisationIdealTimesLattice : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT → ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) → ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  first | exact @GlobalTheory.LevkLoc.congr_of_isAA | exact GlobalTheory.LevkLoc.congr_of_isAA | (intros; apply GlobalTheory.LevkLoc.congr_of_isAA <;> assumption)
