import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle GlobalTheory.ShFam
open GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

def IsLieBase (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X)
    (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) :
    Prop :=
  IsOpenImmersion j ∧ f ≫ j = C.π ∧ Tied e X j f₀ S A₀

def openPart {X : Var F} (j : X.X ⟶ gen Z) : X.X.Opens := j ⁻¹ᵁ (genBd Z).compl

def cxOf (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (y : CxPts X.str (σ.comp e.toRingHom)) : CxPts (genStr Z) σ :=
  ⟨y.1 ≫ j, by
    have : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
    refine (cancel_mono (spMap e.toRingHom)).1 ?_
    rw [Category.assoc, Category.assoc, hj, y.2, ← Spec.map_comp]
    rfl⟩

variable {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def unfFam (U : Formalism.L2.PjFree.Unf Xo c σ r) : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r := fun σ' =>
  if h : σ = σ' then h ▸ U else { Comp := Empty, X := fun k => k.elim, un := fun k => k.elim }

variable (Z) in

def hodgeMet (U : Formalism.L2.PjFree.Unf Xo c σ r) : EigMet Z σ :=
  EigMet.hodge (unfFam U) (2 * Real.pi) Real.two_pi_pos (Classical.arbitrary (EigMet Z σ))

def FrameAt (e : F ≃+* c.F) {X : Var F} {j : X.X ⟶ gen Z} (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) {x : Sp ℂ ⟶ Z.X} (g : EigFrame Z σ x) : Prop :=
  ∃ (φ : c.F →+* X.X.presheaf.stalk (under y)) (fz : EigFrame Z φ (stalkPt X (under y) ≫ j ≫ genι Z))
    (ψ : X.X.presheaf.stalk (under y) →+* ℂ), y.1 = spMap ψ ≫ stalkPt X (under y) ∧
      fz.Coord (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) f₀ (A₀ * A⁻¹) ∧ fz.IsMap ψ g

open Classical in

def lieGram (e : F ≃+* c.F) (U : Formalism.L2.PjFree.Unf Xo c σ r) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ : Mat Dw.mult X.Fn) (A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) : Mat Dw.mult ℂ :=
  if h : ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g then
    fun τ => ((hodgeMet Z U).gram (cxOf e σ hj y) h.choose τ)ᵀ
  else 0

end GlobalTheory.LieBase
