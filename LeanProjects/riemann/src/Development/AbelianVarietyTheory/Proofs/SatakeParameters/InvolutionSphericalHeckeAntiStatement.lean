import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_spherical_hecke_anti : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsIdemAt e P → (∃ θ : GA D V → GA D V, (∀ g, SuppAt e V g → SuppAt e V (θ g)) ∧ (∀ x y, SuppAt e V x → SuppAt e V y → θ (x * y) = θ y * θ x) ∧ (∀ x, SuppAt e V x → θ (θ x) = x) ∧ (∀ k ∈ locPart V (KsphC V ∅) e, θ k ∈ KsphC V ∅) ∧ ∀ g, SuppAt e V g → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, θ g = a * g * b) ∧ (∀ g, SuppAt e V g → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppAt e V γ) ∧ IsCosetRep V (locPart V (KsphC V ∅) e) g R) ∧ ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∀ k, k ≤ V.rank → ∃ α, IsHeckeElt V e (ϖ : D.host.E) k α) ∧ ∀ k α, IsHeckeElt V e (ϖ : D.host.E) k α → IsHeckeElt V (cA D e) (star (ϖ : D.host.E)) k α⁻¹ ∧ ∀ (ϖ' : 𝓞 D.host.E) α', ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → IsHeckeElt V e (ϖ' : D.host.E) k α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  first | exact @GlobalTheory.SplitPlace.split_local | exact GlobalTheory.SplitPlace.split_local | (intros; apply GlobalTheory.SplitPlace.split_local <;> assumption)
