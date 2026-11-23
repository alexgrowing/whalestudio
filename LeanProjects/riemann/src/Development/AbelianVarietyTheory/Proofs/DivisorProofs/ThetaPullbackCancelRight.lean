import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false

open Limits (pullback)

namespace GlobalTheory.PPAS

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) (w' : ψ ≫ A'.hom = A''.hom ≫ g)
    (w'' : (ψ ≫ φ) ≫ A.hom = A''.hom ≫ (g ≫ f)) :
    sqMap w' ≫ sqMap w = sqMap w'' := by
  apply pullback.hom_ext
  · simp only [sqMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    simp only [Category.assoc]
  · simp only [sqMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
    simp only [Category.assoc]

theorem exists_pull_hasTheta_comp : ∀ (S T T' : Scheme.{0}) (P : PPAS S) (P' : PPAS T) (f : T ⟶ S)
    (φ : P'.A.left ⟶ P.A.left) (g : T' ⟶ T), P'.IsPull P f φ →
    (∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P'.A.left), Q.IsPull P' g ψ ∧ Q.HasTheta) →
    ∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (g ≫ f) ψ ∧ Q.HasTheta := by
  rintro S T T' P P' f φ g ⟨h₁, hc₁⟩ ⟨Q, ψ, ⟨h₂, hc₂⟩, hθ⟩
  refine ⟨Q, ψ ≫ φ, ⟨h₂.comp h₁, ?_⟩, hθ⟩
  rw [hc₂, hc₁, ← CechPic.pull_comp, sqMap_comp]

end GlobalTheory.PPAS
