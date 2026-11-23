import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenFrameComp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_toroidal_eigen_frame_comp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → IsIntegral V.toScheme → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (u : Cell.Coord Dw → Γ((Φ.C k).Y.X, Cell.cellOpen (Φ.C k) hV f₀ w)), Cell.IsCoord (Φ.C k) hV f₀ w u → ∀ y : (Φ.C k).Y.X, y ∈ Cell.cellOpen (Φ.C k) hV f₀ w → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ V.toScheme) (a : Cell.Coord Dw → Γ(Spec (.of Ω), ⊤)), ∃ p : Spec (.of Ω) ⟶ (Cell.cellOpen (Φ.C k) hV f₀ w).toScheme, p ≫ Cell.cellMap (Φ.C k) hV f₀ w = x ∧ ∀ i, p.appTop (Cell.coordTop (Φ.C k) hV f₀ w u i) = a i := by
  first | exact @GlobalTheory.ShFam.Cell.exists_cell_pt | exact GlobalTheory.ShFam.Cell.exists_cell_pt | (intros; apply GlobalTheory.ShFam.Cell.exists_cell_pt <;> assumption)
