import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem existsUnique_of_openImmersion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (M : Model b N) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (s₀ : Y₀ ⟶ M.X) (s : Y ⟶ M.X) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), IsOpenImmersion i → i ≫ s = s₀ → m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ) → ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₂ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₂.φ := by
  intro p _ D R _ b N _ _ r w j c M Y₀ Y i s₀ s σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ _ his hsq hfac hU S x o₁ o₁' m₁ ψ₁
    hp hisog htj
  obtain ⟨y₀, ⟨hy₀, m₀, m₂, hsq₀⟩, huniq⟩ := hU S x o₁ o₁' m₁ ψ₁ hp hisog htj
  refine ⟨y₀ ≫ i, ⟨by rw [Category.assoc, his, hy₀], m₀.comp m, m₂.comp m', ?_⟩, ?_⟩
  · show (m₀.φ ≫ m.φ) ≫ ψ.left = ψ₁.left ≫ (m₂.φ ≫ m'.φ)
    rw [Category.assoc, hsq, ← Category.assoc, hsq₀, Category.assoc]
  · rintro y ⟨hy, n₀, n₂, hsqn⟩
    obtain ⟨f₀, rfl⟩ := hfac S y hp
    obtain ⟨k₀, hk₀⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₀ m
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₂ m'
    have hsqk : k₀.φ ≫ ψ₀.left = ψ₁.left ≫ k₂.φ := by
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, hk₀, hsqn, ← hk₂]
      · rw [Category.assoc, Over.w ψ₀, k₀.cart.1.w, Category.assoc, k₂.cart.1.w, ← Category.assoc, Over.w ψ₁]
    have e := huniq f₀ ⟨by rw [← his, ← Category.assoc]; exact hy, k₀, k₂, hsqk⟩
    rw [e]

end GlobalTheory.UPel.HT.ES
