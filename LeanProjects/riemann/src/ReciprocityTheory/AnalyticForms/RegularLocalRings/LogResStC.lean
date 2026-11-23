import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

open AlgebraicGeometry CategoryTheory

universe u

namespace ReciprocityTheory.AnForm.R.FinalTheorems

noncomputable abbrev reesChart {R : Type u} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) :
    Subalgebra R (Localization.Away (g i)) :=
  Algebra.adjoin R (Set.range fun k => IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)))

def ReesCharts {X W : Scheme.{u}} (π : W ⟶ X) (J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, ∃ (m : ℕ) (g : Fin m → Γ(X, U.1)),
    Ideal.span (Set.range g) = J.ideal U ∧
    ∃ V : Fin m → W.Opens, (⨆ i, V i) = π ⁻¹ᵁ U.1 ∧
      ∀ i, ∃ e : (V i).toScheme ≅ Spec (CommRingCat.of (reesChart g i)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (reesChart g i))) ≫ U.2.fromSpec =
          (V i).ι ≫ π

def LogResStC (X : Scheme.{u}) (B : TopologicalSpace.Closeds X) : Prop :=
  ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ B ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) ∧
    Snc (Scheme.IdealSheafData.vanishingIdeal
      ⟨π.base ⁻¹' (B : Set X), IsClosed.preimage π.base.hom.continuous B.2⟩) ∧
    (∀ x : X, SncAt (Scheme.IdealSheafData.vanishingIdeal B) x →
      ∃ f ∈ nonZeroDivisors (X.presheaf.stalk x), stalkId J x = Ideal.span {f}) ∧
    (∃ U : X.Opens, (U : Set X) = {x : X | SncAt (Scheme.IdealSheafData.vanishingIdeal B) x} ∧
      IsIso (π ∣_ U)) ∧
    IsSeparated π ∧ LocallyOfFiniteType π ∧ ReesCharts π J

def GFLogStCR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B

end ReciprocityTheory.AnForm.R.FinalTheorems
