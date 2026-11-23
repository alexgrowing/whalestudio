import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqToStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvFormBC

open GlobalTheory.InvForm

theorem isBaseChange_invForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) := by
  intro R _ A _ g hab hdim U
  let f := evForm A.hom U ∘ₗ (InvForm A).subtype
  let L := f.liftBaseChange (Sec A.hom U.unop.1)
  have hs : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp [L, f]⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine R A g hab hdim U
  have hl : ∀ x, r (L x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      have : L (b ⊗ₜ w) = b • evForm A.hom U w.1 := by simp [L, f]
      rw [this, map_smul, hr, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective L := fun x y h ↦ by rw [← hl x, ← hl y, h]
  have hb : Function.Bijective L := ⟨hi, hs⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L hb) fun x ↦
    show L (1 ⊗ₜ x) = f x from (LinearMap.liftBaseChange_tmul _ f 1 x).trans (one_smul _ _)

theorem exists_invariant_frame : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (j : M →ₗ[R] GlobForm A.hom), Module.Finite R M ∧ Module.Projective R M ∧ ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ j) := by
  intro R _ A _ g hab hdim
  have hbc := isBaseChange_invForm R A g hab hdim
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective R A g hab hdim hbc
  exact ⟨InvForm A, inferInstance, inferInstance, (InvForm A).subtype, hfin, hproj, hbc⟩

end GlobalTheory.InvFormBC
