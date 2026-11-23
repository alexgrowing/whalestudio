import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionsUniqueDecomposition
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpThickening

open GlobalTheory.RelConstThickening

theorem existsUnique_affine {R : Type} [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R))
    (p₂ : P ⟶ Z) (H : IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))))
    {V : Z.Opens} (hV : IsAffineOpen V) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := R) (constHom h V) (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    simp
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]

theorem existsUnique_decomp : ∀ (R : Type) [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R)) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))) → ∀ (O : Z.Opens) (F : Γ(P, p₂ ⁻¹ᵁ O)), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun _ _ _ _ h p₁ p₂ H O F =>
    existsUnique_comb (W := ⊤) (fun _ hV _ F => existsUnique_affine h p₁ p₂ H hV F) O le_top F

end GlobalTheory.SpThickening

end
