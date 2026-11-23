import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpTr :
    OpTr.{u} := by
  intro B R _ T hT Z Y Z' p q p' s t hs ht tr htr A
  have key : ∀ (W : Scheme) (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y))
      (hσ : ∀ j, σ j ≫ q = c ≫ p), Splits s c σ → ∀ x,
      T.pull c rfl ((tr ∘ₗ T.pull t ht) x) = ∑ j, T.pull (σ j ≫ t)
        (by rw [Category.assoc, ht]; exact hσ j) x := by
    intro W c J _ σ hσ hspl x
    rw [LinearMap.comp_apply, htr W (c ≫ p) c rfl J σ hσ hspl]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (T.pull_comp (σ j) t (hσ j) ht _ x).symm
  constructor
  · rintro ⟨W, c, G, _, _, a, J, _, σ, h, hgal, hspl, hA⟩
    have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
      rw [← ht, ← Category.assoc]
      exact h j
    apply LinearMap.ext
    intro x
    apply hT.inj p (c ≫ p) c rfl G a hgal
    rw [hA x, key W c J σ hσ hspl x]
  · rintro ⟨W, c, G, _, _, a, J, _, σ, hgal, hspl⟩ rfl
    have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
      rw [← hs, ← Category.assoc, hspl.1 j]
    refine ⟨W, c, G, inferInstance, inferInstance, a, J, inferInstance, σ,
      fun j => by rw [Category.assoc, ht]; exact hσ j, hgal, hspl, fun x => ?_⟩
    exact key W c J σ hσ hspl x
