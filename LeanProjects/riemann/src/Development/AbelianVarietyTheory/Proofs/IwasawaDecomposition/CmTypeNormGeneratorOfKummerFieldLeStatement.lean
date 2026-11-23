import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTypeNorm_generator_of_kummerField_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  first | exact @GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | exact GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | (intros; apply GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le <;> assumption)
