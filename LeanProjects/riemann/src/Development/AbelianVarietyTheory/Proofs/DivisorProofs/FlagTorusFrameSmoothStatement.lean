import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_torus_frame_smooth : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (ψ : Γ(gen Z, V) →+* R) (a : Cell.Coord Dw → R), Cell.Lands Φ hV f₀ w i ((algebraMap R K).comp ψ) (algebraMap R K ∘ a) → Cell.Lands Φ hV f₀ w i ((IsLocalRing.residue R).comp ψ) (IsLocalRing.residue R ∘ a) := by
  first | exact @GlobalTheory.ShFam.Cell.Lands.residue_of_fraction | exact GlobalTheory.ShFam.Cell.Lands.residue_of_fraction | (intros; apply GlobalTheory.ShFam.Cell.Lands.residue_of_fraction <;> assumption)
