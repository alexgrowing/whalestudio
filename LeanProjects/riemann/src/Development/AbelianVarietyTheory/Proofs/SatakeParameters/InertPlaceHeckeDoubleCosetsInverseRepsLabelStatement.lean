import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_hecke_double_cosets_inverse_reps_label : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsPrimeIdem P e e → (∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → ∀ g, SuppF V e g → (∃ a b, a ∈ KsphC V ∅ ∧ SuppF V e a ∧ b ∈ KsphC V ∅ ∧ SuppF V e b ∧ g⁻¹ = a * g * b) ∧ (∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V e γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V e k} g R) ∧ ∀ (ϖ ϖ' : 𝓞 D.host.E) d g', ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → SuppF V e g' → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ' : D.host.E) d g' → ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V e a ∧ b ∈ KsphC V ∅ ∧ SuppF V e b ∧ g' = a * g * b := by
  first | exact @GlobalTheory.InertDoubleCoset.inert_double_cosets | exact GlobalTheory.InertDoubleCoset.inert_double_cosets | (intros; apply GlobalTheory.InertDoubleCoset.inert_double_cosets <;> assumption)
