import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentStructureMapSpec
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameIn
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_component_structure_map_spec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}, ∀ (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (u : Cell.Coord Dw → Γ(C.Y.X, Cell.cellOpen C hV f₀ w)), Cell.IsCoord C hV f₀ w u → ∀ (Ω : Type) [Field Ω] (ψ : Γ(gen Z, V) →+* Ω) (x : Sp Ω ⟶ gen Z) (hx : spMap ψ ≫ hV.fromSpec = x) (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (a : Cell.Coord Dw → Ω), Cell.FrameIn hV f₀ w ψ hx g a → ∀ p : Sp Ω ⟶ C.Y.X, p ≫ C.π = x → C.Carries p g → ∃ q : Sp Ω ⟶ (Cell.cellOpen C hV f₀ w).toScheme, q ≫ (Cell.cellOpen C hV f₀ w).ι = p ∧ ∀ i, (Scheme.ΓSpecIso (.of Ω)).hom (q.appTop (Cell.coordTop C hV f₀ w u i)) = a i := by
  first | exact @GlobalTheory.ShFam.Cell.mem_cellOpen_of_carries | exact GlobalTheory.ShFam.Cell.mem_cellOpen_of_carries | (intros; apply GlobalTheory.ShFam.Cell.mem_cellOpen_of_carries <;> assumption)
