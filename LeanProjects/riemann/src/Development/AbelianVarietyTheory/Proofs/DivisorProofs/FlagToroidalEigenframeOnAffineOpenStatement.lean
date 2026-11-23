import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenframeOnAffineOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameIn
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_toroidal_eigenframe_on_affine_open : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}, ∀ {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → IsIntegral V.toScheme → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (y : (Φ.C k).Y.X), y ∈ Cell.cellOpen (Φ.C k) hV f₀ w → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ψ : Γ(gen Z, V) →+* Ω) (x : Sp Ω ⟶ gen Z) (hx : spMap ψ ≫ hV.fromSpec = x) (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (a : Cell.Coord Dw → Ω), Cell.FrameIn hV f₀ w ψ hx g a → ∀ (i : U.Comp) (p : Sp Ω ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → i = k := by
  first | exact @GlobalTheory.ShFam.Cell.mem_comp_of_frameIn | exact GlobalTheory.ShFam.Cell.mem_comp_of_frameIn | (intros; apply GlobalTheory.ShFam.Cell.mem_comp_of_frameIn <;> assumption)
