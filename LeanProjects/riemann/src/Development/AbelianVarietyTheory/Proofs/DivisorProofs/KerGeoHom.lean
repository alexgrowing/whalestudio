import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameIn

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

section Geo

variable {P : Type} [CommRing P]

abbrev GeoF (t : PrimeSpectrum P) : Type := AlgebraicClosure t.asIdeal.ResidueField

def geoHom (t : PrimeSpectrum P) : P →+* GeoF t :=
  (algebraMap t.asIdeal.ResidueField (GeoF t)).comp (algebraMap P t.asIdeal.ResidueField)

theorem ker_geoHom (t : PrimeSpectrum P) : RingHom.ker (geoHom t) = t.asIdeal := by
  rw [geoHom, RingHom.ker_comp_of_injective _ (algebraMap t.asIdeal.ResidueField (GeoF t)).injective]
  exact Ideal.ker_algebraMap_residueField t.asIdeal

end Geo

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

def Lands (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp)
    {K : Type} [Field K] (ψ : Γ(gen Z, V) →+* K) (a : Coord Dw → K) : Prop :=
  ∃ g : EigFrame Z (ψ.comp φV) ((spMap ψ ≫ hV.fromSpec) ≫ genι Z), FrameIn hV f₀ w ψ rfl g a ∧
    ∃ p : Sp K ⟶ (Φ.C i).Y.X, p ≫ (Φ.C i).π = spMap ψ ≫ hV.fromSpec ∧ (Φ.C i).Carries p g

def InComp (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp)
    (t : PrimeSpectrum (MvPolynomial (Coord Dw) Γ(gen Z, V))) : Prop :=
  Lands Φ hV f₀ w i ((geoHom t).comp MvPolynomial.C) (fun j => geoHom t (MvPolynomial.X j))

end Pt

end GlobalTheory.ShFam.Cell
