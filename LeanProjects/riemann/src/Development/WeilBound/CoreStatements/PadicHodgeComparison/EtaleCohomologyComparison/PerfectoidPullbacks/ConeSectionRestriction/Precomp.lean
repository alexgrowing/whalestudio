import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def CLiftK.precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) : CLiftK (h ⋙ g) D where
  p c := Λ.p (h.obj c)
  hp c := Λ.hp (h.obj c)
  w φ := Λ.w (h.map φ)
  hw φ hh := Λ.hw (h.map φ) hh

def zK {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ) :
    CH.Cn (g ⋙ O (smFun X q)) 2 :=
  fun σ => (show (g.obj (σ.obj (Fin.last 2))).B from
    plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1))

def 𝒱D (D : E.LineData X) : Set X.Opens := {V | ∃ σ : (V : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = V.ι}

end CrystallineSemistableComparison.Pb
