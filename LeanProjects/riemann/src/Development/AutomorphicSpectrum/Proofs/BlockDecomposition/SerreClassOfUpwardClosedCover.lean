import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

theorem serre_of_equiv {R : Type} [CommRing R] (𝒮 : Serre.{1} R) {M N : Type 1} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : 𝒮.P M) : 𝒮.P N := by
  refine 𝒮.mid M N PUnit.{2} e.toLinearMap 0 ?_ h (𝒮.zero PUnit.{2} inferInstance)
  intro y
  exact iff_of_true (Subsingleton.elim _ _) ⟨e.symm y, e.apply_symm_apply y⟩

theorem serre_union : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((cechH F W q).cx.H p)) → 𝒮.P (HU F (fun T => ∃ α, W α T) n) := by
  intro R _ C _ F ι W hW 𝒮 n h
  have hle : ∀ α, W α ≤ (fun T => ∃ β, W β T : ObjectProperty C) := fun α T hT => ⟨α, hT⟩
  refine GlobalTheory.T.serre_class_of_cech_spectral_sequence ((ObjectProperty.ι (fun T => ∃ β, W β T : ObjectProperty C)) ⋙ F)
    (fun α T => W α T.obj) (fun α => by
      intro T T' f hT
      exact hW α f.hom hT T'.property) (fun T => T.property) 𝒮 n ?_
  intro p q hpq
  obtain ⟨e⟩ := GlobalTheory.T.cech_cohomology_full_subcategory_iso F (fun T => ∃ β, W β T : ObjectProperty C) W hle q p
  exact serre_of_equiv 𝒮 e.symm (h p q hpq)

end GlobalTheory.CompanionTheory.CosieveRel
