import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameTransition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_torus_frame_transition : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ψ : Γ(gen Z, V) →+* Ω) (a : Cell.Coord Dw → Ω), Cell.Lands Φ hV f₀ w i ψ a → ∀ (x : Sp Ω ⟶ gen Z) (hx : spMap ψ ≫ hV.fromSpec = x) (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)), Cell.FrameIn hV f₀ w ψ hx g a → ∀ (j : U.Comp) (p : Sp Ω ⟶ (Φ.C j).Y.X), p ≫ (Φ.C j).π = x → (Φ.C j).Carries p g → j = i := by
  first | exact @GlobalTheory.ShFam.Cell.lands_unique | exact GlobalTheory.ShFam.Cell.lands_unique | (intros; apply GlobalTheory.ShFam.Cell.lands_unique <;> assumption)
