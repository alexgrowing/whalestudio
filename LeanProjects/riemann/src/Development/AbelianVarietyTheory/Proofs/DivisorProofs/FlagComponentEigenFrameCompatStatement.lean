import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentEigenFrameCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_component_eigen_frame_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ y : C.Y.X, C.π y ∈ V → ∃ w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), y ∈ Cell.cellOpen C hV f₀ w := by
  first | exact @GlobalTheory.ShFam.Cell.mem_cellOpen | exact GlobalTheory.ShFam.Cell.mem_cellOpen | (intros; apply GlobalTheory.ShFam.Cell.mem_cellOpen <;> assumption)
