import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameComposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_composition : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} (f : EigFrame Z φ x) (g : EigFrame Z φ' x') (k : EigFrame Z φ'' x'') (ψ : R →+* R') (χ : R' →+* R'') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) (s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R''ˣ), f.Tri ψ g t → g.Tri χ k s → f.Tri (χ.comp ψ) k (fun τ i => Units.map χ.toMonoidHom (t τ i) * s τ i) := by
  first | exact @GlobalTheory.FrameTri.tri_trans | exact GlobalTheory.FrameTri.tri_trans | (intros; apply GlobalTheory.FrameTri.tri_trans <;> assumption)
