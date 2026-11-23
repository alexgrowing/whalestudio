import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

namespace FinalTheorems

def GFLogStC : Prop :=
  ∀ (X : Scheme.{0}) [IsNoetherian X], (∃ f : X ⟶ Spec (CommRingCat.of ℂ), LocallyOfFiniteType f) →
    QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B

theorem gfLogStC_of_CR (h : GFLogStCR.{0}) : GFLogStC := fun X _ _ a b c B d e => h X a b c B d e

end FinalTheorems

def ProjLogResC : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P), IsMultiHomogIdeal D → P.IsRadical →
    (∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0) →
    (∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q) → FinalTheorems.LogResStC (projX P hP) (projB P D hP)

theorem projLogResC_of_C (hC : FinalTheorems.GFLogStC) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC :=
  fun _ _ _ _ _ P _ hP hD hrad hsing hmin =>
    hC (projX P hP) ⟨toSpecC hP, inferInstance⟩ (qe_projX hP hQ) (isReduced_projX hP hrad) (fFinRes_projX hP) _
      (sing_subset_projB hP hD hQ hsing) (interior_projB hP hD hmin)

theorem projLogResC_of_CR (hC : FinalTheorems.GFLogStCR.{0}) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC :=
  projLogResC_of_C (FinalTheorems.gfLogStC_of_CR hC) hQ

end ReciprocityTheory.AnForm.R
