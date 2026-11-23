import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameWeylPermutationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCompositionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem lands_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) {K K' : Type} [Field K] [Field K'] (em : K →+* K') (ψ : Γ(gen Z, V) →+* K) (a : Cell.Coord Dw → K), Cell.Lands Φ hV f₀ w i ψ a → Cell.Lands Φ hV f₀ w i (em.comp ψ) (em ∘ a) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ V hV φV f₀ w i K K' _ _ em ψ a h
  have hsp : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R''),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro R R' R'' _ _ _ f g
    first | rfl | (simp [spMap]) | (exact Spec.map_comp _ _)
  obtain ⟨g, hg, p, hp, y, ψ', φ₁, f, t₀, t', hpy, hf0, hfg⟩ := h
  obtain ⟨g', hg'⟩ := exists_frameIn hV f₀ w (em.comp ψ) rfl (em ∘ a)
  obtain ⟨t, ht⟩ := GlobalTheory.T.eigen_frame_weyl_permutation hV f₀ w em ψ rfl rfl g g' a hg hg'
  refine ⟨g', hg', spMap em ≫ p, ?_, y, em.comp ψ', φ₁, f, t₀, _, ?_, hf0,
    GlobalTheory.T.eigen_frame_composition f g g' ψ' em t' t hfg ht⟩
  · rw [Category.assoc, hp, hsp, Category.assoc]
  · rw [hpy, hsp, Category.assoc]

end GlobalTheory.ShFam.Cell
