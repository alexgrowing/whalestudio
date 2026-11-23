import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameWeylPermutation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_weyl_permutation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, ∀ {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {R R' : Type} [CommRing R] [CommRing R'] (ν : R →+* R') (ψ : Γ(gen Z, V) →+* R) {x : Sp R ⟶ gen Z} (hx : spMap ψ ≫ hV.fromSpec = x) {x' : Sp R' ⟶ gen Z} (hx' : spMap (ν.comp ψ) ≫ hV.fromSpec = x') (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (g' : EigFrame Z ((ν.comp ψ).comp φV) (x' ≫ genι Z)) (a : Cell.Coord Dw → R), Cell.FrameIn hV f₀ w ψ hx g a → Cell.FrameIn hV f₀ w (ν.comp ψ) hx' g' (ν ∘ a) → ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ, g.Tri ν g' t := by
  first | exact @GlobalTheory.ShFam.Cell.frameIn_tri | exact GlobalTheory.ShFam.Cell.frameIn_tri | (intros; apply GlobalTheory.ShFam.Cell.frameIn_tri <;> assumption)
