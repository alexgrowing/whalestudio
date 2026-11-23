import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentEigenframeOnAffineOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_component_eigenframe_on_affine_open : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) {U : C.Y.X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ C.π ⁻¹ᵁ V) (hg : genericPoint C.Y.X ∈ U) {φ : c.F →+* Γ(C.Y.X, U)} (fr : EigFrame Z φ ((hU.fromSpec ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (hx : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec ≫ genι Z = (hU.fromSpec ≫ C.π) ≫ genι Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U)), (hU.fromSpec ≫ C.π) ≫ genStr Z = spMap φ → fr.Tri (fnOf U hg) C.f0 t → (∀ τ i, fr.vec τ i = ∑ k, A τ i k • GlobalTheory.LieLocFrame.res (C.π.appLE V U hUV).hom hx (f₀.vec τ k)) → ∀ {U' : C.Y.X.Opens} (hU' : IsAffineOpen U') (hle : U' ≤ U), genericPoint C.Y.X ∈ U' → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (a : ∀ τ : E →+* ℂ, GlobalTheory.ShFam.Cell.Above (Dw.mult τ) → Γ(C.Y.X, U')), (∀ τ, GlobalTheory.ShFam.Cell.InCell ((A τ).map (C.Y.X.presheaf.map (homOfLE hle).op).hom) (w τ) (a τ)) → GlobalTheory.ShFam.Cell.CellAt C hV f₀ w U' a := by
  first | exact @GlobalTheory.ShFam.Cell.cellAt_restrict | exact GlobalTheory.ShFam.Cell.cellAt_restrict | (intros; apply GlobalTheory.ShFam.Cell.cellAt_restrict <;> assumption)
