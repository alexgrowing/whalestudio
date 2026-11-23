import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)), IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧ (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧ ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  first | exact @GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | exact GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | (intros; apply GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr <;> assumption)
