import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsLowInv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

section Mat
variable {R : Type} [CommRing R] {m : ℕ}

theorem inCell_upMat (w : Equiv.Perm (Fin m)) (a : Above m → R) :
    InCell ((upMat a).submatrix id w.symm) w a := by
  refine ⟨1, ⟨fun i j h => Matrix.one_apply_ne h.ne, fun i => by simp⟩, ?_⟩
  ext i j
  simp

end Mat

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

def FrameIn {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {R : Type}
    [CommRing R] (ψ : Γ(gen Z, V) →+* R) {x : Sp R ⟶ gen Z} (hx : spMap ψ ≫ hV.fromSpec = x) {φ : c.F →+* R}
    (g : EigFrame Z φ (x ≫ genι Z)) (a : Coord Dw → R) : Prop :=
  ∃ A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R,
    (∀ τ i, g.vec τ i = ∑ k, A τ i k • GlobalTheory.LieLocFrame.res (x' := x ≫ genι Z) ψ (by rw [← hx, Category.assoc]) (f₀.vec τ k)) ∧
    ∀ τ, InCell (A τ) (w τ) (fun p => a ⟨τ, p⟩)

theorem exists_frameIn {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {R : Type}
    [CommRing R] (ψ : Γ(gen Z, V) →+* R) {x : Sp R ⟶ gen Z} (hx : spMap ψ ≫ hV.fromSpec = x) (a : Coord Dw → R) :
    ∃ g : EigFrame Z (ψ.comp φV) (x ≫ genι Z), FrameIn hV f₀ w ψ hx g a := by
  have hx' : spMap ψ ≫ hV.fromSpec ≫ genι Z = x ≫ genι Z := by rw [← hx, Category.assoc]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ShFam.Spread.exists_bc f₀ ψ rfl hx'
  let A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R :=
    fun τ => (upMat (fun p => a ⟨τ, p⟩)).submatrix id (w τ).symm
  have hdet : ∀ τ, IsUnit (A τ).det := fun τ => by
    simp only [A, Matrix.det_permute', det_upMat, mul_one]
    exact ((Equiv.Perm.sign (w τ).symm).isUnit.map (Int.castRingHom R))
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.Spread.exists_change f₁ A (fun τ => (A τ)⁻¹)
    (fun τ => Matrix.nonsing_inv_mul _ (hdet τ))
  refine ⟨g, A, fun τ i => ?_, fun τ => inCell_upMat _ _⟩
  rw [hg τ i]
  simp only [hf₁]

end Pt

end GlobalTheory.ShFam.Cell
