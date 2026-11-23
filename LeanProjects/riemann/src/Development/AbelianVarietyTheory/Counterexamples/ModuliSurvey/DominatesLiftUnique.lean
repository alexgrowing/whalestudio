import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section

namespace GlobalTheory.ModelRelProbe

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem j_over {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  unfold Model.j
  rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem transition_over {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O O₂ : Type} [CommRing O] [CommRing O₂]
    {β : O →+* c.F} {β₂ : O₂ →+* c₂.F} (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (b : O →+* O₂) (π : Y₂.X ⟶ Y.X)
    (h : IsTransition Y Y₂ b π) [Mono (spMap β)] (σ : c.F →+* c₂.F) (hσ : σ.comp β = β₂.comp b) :
    π ≫ Y.s = Y₂.s ≫ spMap b ∧ ∃ r : Xo₂.XF c₂ ⟶ Xo.XF c, Y₂.j ≫ π = r ≫ Y.j ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap σ := by
  obtain ⟨π', -, r, h₁, h₂, -, h₃, -⟩ := h
  have e : π ≫ Y.s = Y₂.s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨e, r, h₃, ?_⟩
  rw [← cancel_mono (spMap β), Category.assoc, Category.assoc, ← j_over, ← Category.assoc, ← h₃, Category.assoc, e,
    ← Category.assoc, j_over, Category.assoc, spMap_comp, spMap_comp, hσ]

end GlobalTheory.ModelRelProbe
