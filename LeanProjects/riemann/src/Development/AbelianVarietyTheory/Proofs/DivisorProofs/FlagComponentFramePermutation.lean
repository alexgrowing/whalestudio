import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellAtCoordEqInf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

theorem exists_isCoord (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    ∃ u : Coord Dw → Γ(C.Y.X, cellOpen C hV f₀ w), IsCoord C hV f₀ w u := by
  let X : Scheme := C.Y.X
  let ι := {q : Σ U : X.Opens, (∀ τ : E →+* ℂ, Above (Dw.mult τ) → Γ(X, U)) // CellAt C hV f₀ w q.1 q.2}
  let Ui : ι → X.Opens := fun i => i.1.1
  have hle : ∀ i : ι, Ui i ≤ cellOpen C hV f₀ w := fun i => le_sSup ⟨i.1.2, i.2⟩
  have hcov : cellOpen C hV f₀ w ≤ iSup Ui :=
    sSup_le fun U ⟨a, h⟩ => le_iSup Ui (⟨⟨U, a⟩, h⟩ : ι)
  have hglue : ∀ (τ : E →+* ℂ) (p : Above (Dw.mult τ)), ∃ s : Γ(X, cellOpen C hV f₀ w),
      ∀ i : ι, X.presheaf.map (homOfLE (hle i)).op s = i.1.2 τ p := fun τ p => by
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' Ui (cellOpen C hV f₀ w) (fun i => homOfLE (hle i)) hcov
      (fun i => i.1.2 τ p) (fun i j => cellAt_coord_eq_inf C hV f₀ w _ _ _ _ i.2 j.2 τ p)
    exact ⟨s, hs⟩
  choose u hu using hglue
  exact ⟨fun q => u q.1 q.2, fun U a h hle' τ p => hu τ p ⟨⟨U, a⟩, h⟩⟩

end Geo

end GlobalTheory.ShFam.Cell
