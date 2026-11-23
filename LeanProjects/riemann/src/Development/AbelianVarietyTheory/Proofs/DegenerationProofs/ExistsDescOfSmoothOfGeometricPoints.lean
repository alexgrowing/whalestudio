import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory

theorem exists_desc_of_smooth_of_geometricPoints :
    ∀ (K C : Type) [Field K] [CharZero K] [Field C] [Algebra K C] (X Y : Over (Sp K)), Smooth X.hom → IsSeparated Y.hom → ∀ f : pullback X.hom (spMap (algebraMap K C)) ⟶ Y.left, f ≫ Y.hom = pullback.fst X.hom (spMap (algebraMap K C)) ≫ X.hom → (∀ (F : Type) [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ pullback X.hom (spMap (algebraMap K C))), x ≫ pullback.fst _ _ = x' ≫ pullback.fst _ _ → x ≫ f = x' ≫ f) → ∃ f₀ : X ⟶ Y, pullback.fst X.hom (spMap (algebraMap K C)) ≫ f₀.left = f := by
  intro K C _ _ _ _ X Y hX hY f hf H
  have : IsReduced (pullback X.hom (spMap (algebraMap K C))) :=
    isReduced_of_smooth_of_isReduced (pullback.snd X.hom (spMap (algebraMap K C)))
  obtain ⟨ψ, hψ⟩ := ArcDataDescent.exists_desc_of_points (algebraMap K C)
    (IsPullback.of_hasPullback X.hom (spMap (algebraMap K C))) Y.hom f X.hom hf H
  have f₁ : Flat (spMap (algebraMap K C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective (spMap (algebraMap K C)) :=
    ⟨fun y => ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi (pullback.fst X.hom (spMap (algebraMap K C))) := Flat.epi_of_flat_of_surjective _
  refine ⟨Over.homMk ψ ?_, hψ⟩
  rw [← cancel_epi (pullback.fst X.hom (spMap (algebraMap K C))), ← Category.assoc, hψ]
  exact hf

end GlobalTheory
