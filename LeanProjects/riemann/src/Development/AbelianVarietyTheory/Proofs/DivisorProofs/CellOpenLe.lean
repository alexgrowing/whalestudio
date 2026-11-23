import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

abbrev Above (m : ℕ) : Type := {p : Fin m × Fin m // p.1 < p.2}

def IsLowInv (L : Matrix (Fin m) (Fin m) R) : Prop := (∀ i j, i < j → L i j = 0) ∧ ∀ i, IsUnit (L i i)

def upMat (a : Above m → R) : Matrix (Fin m) (Fin m) R := fun i j =>
  if h : i < j then a ⟨(i, j), h⟩ else if i = j then 1 else 0

def InCell (M : Matrix (Fin m) (Fin m) R) (w : Equiv.Perm (Fin m)) (a : Above m → R) : Prop :=
  ∃ L, IsLowInv L ∧ M.submatrix id w = L * upMat a

end Mat

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

abbrev Coord (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Above (Dw.mult τ)

def CellAt (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (U : C.Y.X.Opens) (a : ∀ τ : E →+* ℂ, Above (Dw.mult τ) → Γ(C.Y.X, U)) : Prop :=
  ∃ (hU : IsAffineOpen U) (hUV : U ≤ C.π ⁻¹ᵁ V) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U))
    (fr : EigFrame Z φ ((hU.fromSpec ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
    (hx : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec ≫ genι Z = (hU.fromSpec ≫ C.π) ≫ genι Z)
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(C.Y.X, U)),
    (hU.fromSpec ≫ C.π) ≫ genStr Z = spMap φ ∧ fr.Tri (fnOf U hg) C.f0 t ∧
    (∀ τ i, fr.vec τ i = ∑ k, A τ i k • GlobalTheory.LieLocFrame.res (C.π.appLE V U hUV).hom hx (f₀.vec τ k)) ∧
    ∀ τ, InCell (A τ) (w τ) (a τ)

def cellOpen (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) : C.Y.X.Opens :=
  sSup {U | ∃ a, CellAt C hV f₀ w U a}

theorem cellOpen_le (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    cellOpen C hV f₀ w ≤ C.π ⁻¹ᵁ V :=
  sSup_le fun _ ⟨_, _, hUV, _⟩ => hUV

def cellMap (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    (cellOpen C hV f₀ w).toScheme ⟶ V.toScheme :=
  C.π.resLE V _ (cellOpen_le C hV f₀ w)

theorem cellMap_ι (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    cellMap C hV f₀ w ≫ V.ι = (cellOpen C hV f₀ w).ι ≫ C.π :=
  Scheme.Hom.resLE_comp_ι _ _

def IsCoord (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (u : Coord Dw → Γ(C.Y.X, cellOpen C hV f₀ w)) : Prop :=
  ∀ (U : C.Y.X.Opens) (a : ∀ τ : E →+* ℂ, Above (Dw.mult τ) → Γ(C.Y.X, U)), CellAt C hV f₀ w U a →
    ∀ (hle : U ≤ cellOpen C hV f₀ w) (τ : E →+* ℂ) (p : Above (Dw.mult τ)),
      C.Y.X.presheaf.map (homOfLE hle).op (u ⟨τ, p⟩) = a τ p

def coordTop (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)))
    (u : Coord Dw → Γ(C.Y.X, cellOpen C hV f₀ w)) (i : Coord Dw) : Γ((cellOpen C hV f₀ w).toScheme, ⊤) :=
  (cellOpen C hV f₀ w).topIso.inv (u i)

end Geo

end GlobalTheory.ShFam.Cell
