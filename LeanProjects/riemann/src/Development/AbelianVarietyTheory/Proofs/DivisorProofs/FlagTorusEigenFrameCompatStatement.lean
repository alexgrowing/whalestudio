import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusEigenFrameCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_torus_eigen_frame_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) {K K' : Type} [Field K] [Field K'] (em : K →+* K') (ψ : Γ(gen Z, V) →+* K) (a : Cell.Coord Dw → K), Cell.Lands Φ hV f₀ w i ψ a → Cell.Lands Φ hV f₀ w i (em.comp ψ) (em ∘ a) := by
  first | exact @GlobalTheory.ShFam.Cell.lands_map | exact GlobalTheory.ShFam.Cell.lands_map | (intros; apply GlobalTheory.ShFam.Cell.lands_map <;> assumption)
