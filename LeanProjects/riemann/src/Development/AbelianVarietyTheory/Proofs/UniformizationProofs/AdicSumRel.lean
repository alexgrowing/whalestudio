import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.UU

theorem finsum_rel {A : Type*} [CommRing A] {Ix Ix' : Type*} (σ : Ix ≃ Ix') (f : Ix → A) (g : Ix' → A)
    (a b v : A) (s : Finset Ix) (s' : Finset Ix') (hf : ∀ i ∉ s, f i = 0) (hg : ∀ i ∉ s', g i = 0)
    (h : ∀ i, a * g (σ i) = b * (f i * v)) :
    a * ∑ i ∈ s', g i = b * ((∑ i ∈ s, f i) * v) := by
  classical
  have h1 : ∑ i ∈ s, f i = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
  have h2 : ∑ i ∈ s', g i = ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) := by
    rw [Finset.sum_map]; simp
  have h3 : ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, g (σ i) :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg _ (fun hm => hi (by
      rw [Finset.mem_map]; exact ⟨σ i, hm, by simp⟩)))
  rw [h1, h2, h3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem adicSum_rel : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y Y₂ : Over (Spec (CommRingCat.of R))) (τ : Y ⟶ Y₂) (X : Scheme.{0}) (L : LB X) (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂.left ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y.left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y.left ⟶ X)) (εu : K'' → ℤ) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y.left, ⊤)) (Ix Ix' : Type) (σ : Ix ≃ Ix') (p : Ix → LB.Sec (LB.LinComb L φ ε)) (p' : Ix' → LB.Sec (LB.LinComb L φ' ε')) (S S'), AdicSum I p S → AdicSum I p' S' → (∀ i (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J → gs r z ⊤ c' * sval (p' (σ i)) r z J = gs r z ⊤ c * (sval (p i) (r ≫ τ.left) z J * (val u r z J).val)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Y.left), Lvl I e (r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval S' r z J = gs r z ⊤ c * (sval S (r ≫ τ.left) z J * (val u r z J).val) := by
  intro R _ I Y Y₂ τ X L K K' K'' _ _ _ φ ε φ' ε' φu εu u c c' Ix Ix' σ p p' S S' hS hS' h e Z r hr z J hJ
  obtain ⟨s, hs⟩ := hS e
  obtain ⟨s', hs'⟩ := hS' e
  have hr2 : Lvl I e ((r ≫ τ.left) ≫ Y₂.hom) := by
    rw [Category.assoc, Over.w τ]; exact hr
  obtain ⟨a1, a2⟩ := hs Z (r ≫ τ.left) hr2 z J hJ
  obtain ⟨b1, b2⟩ := hs' Z r hr z J hJ
  rw [a2, b2]
  exact finsum_rel σ _ _ _ _ _ s s' a1 b1 (fun i => h i Z r z J hJ)

end GlobalTheory.UU
