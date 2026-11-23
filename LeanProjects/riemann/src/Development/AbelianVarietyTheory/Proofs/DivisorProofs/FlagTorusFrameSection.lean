import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Cell

theorem exists_lands : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ψ : Γ(gen Z, V) →+* Ω) (a : Cell.Coord Dw → Ω), ∃ i, Cell.Lands Φ hV f₀ w i ψ a := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ V hV φV f₀ hV' w Ω _ _ ψ a
  obtain ⟨g, hg⟩ := exists_frameIn hV f₀ w ψ rfl a
  have hx : (spMap ψ ≫ hV.fromSpec) ≫ genStr Z = spMap (ψ.comp φV) := by
    rw [Category.assoc, hV']
    exact Spec.map_comp _ _ |>.symm
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts Ω (ψ.comp φV) (spMap ψ ≫ hV.fromSpec) hx g
  exact ⟨i, g, hg, p, hp, hc⟩

end GlobalTheory.ShFam.Cell
