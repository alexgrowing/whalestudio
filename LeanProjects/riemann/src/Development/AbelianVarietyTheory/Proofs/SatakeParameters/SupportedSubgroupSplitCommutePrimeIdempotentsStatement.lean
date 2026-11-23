import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents : ∀ {D : D7} (V : HSp D), (∀ f : Formalism.L2.Theta.AE D, f * f = f → cA D f = f → (∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g) ∧ (∀ g : GA D V, ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂) ∧ ∀ f' g g', f * f' = 0 → SuppF V f g → SuppF V f' g' → Commute g g') ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → f * f = f ∧ cA D f = f ∧ (∀ g, SuppF V f g → g ∈ GfC V) ∧ (∀ e' f', IsPrimeIdem P e' f' → e' = e ∧ f' = f) ∧ ∀ P' e' f', IsPrimeIdem P' e' f' → f * f' = 0 ∨ (f' = f ∧ (P' = P ∨ Formalism.IndefR.Lev.IsConjPl P P'))) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) P' e, IsIdemAt e P → Formalism.IndefR.Lev.IsConjPl P P' → IsIdemAt (cA D e) P' := by
  first | exact @GlobalTheory.IdemSupport.supported_group_and_prime_idempotents | exact GlobalTheory.IdemSupport.supported_group_and_prime_idempotents | (intros; apply GlobalTheory.IdemSupport.supported_group_and_prime_idempotents <;> assumption)
