import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.AbCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preU (U : X.affineOpens) : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, U.2.preimage φ⟩

theorem preU_mono : Monotone (preU φ) := fun _ _ h _ hx ↦ h hx

def prePair (U : X.affineOpens) : Pair φ := ⟨(preU φ U, U), le_rfl⟩

def preAff : AffOp X ⥤ AffOp X' := (preU_mono φ).functor.op

abbrev OPre (s' : X' ⟶ Sp R') : AffOp X ⥤ CommAlgCat.{0} R' := preAff φ ⋙ OAff s'

def preRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPre φ s') := CoefMap.restrict _ _

def preα (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (U : AffOp X) : (OAff s).obj U →+* (OPre φ s').obj U :=
  secPull s s' (prePair φ U.unop)

variable {φ} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

def preCoef (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPre φ s') where
  G := 𝟭 _
  α U := preα φ s s' U
  naturality {p q} a b := (pairPull h).naturality
    (homOfLE (show prePair φ q.unop ≤ prePair φ p.unop from
      ⟨preU_mono φ (leOfHom a.unop), leOfHom a.unop⟩)).op b
  smul U := semiHom_secPull h (prePair φ U.unop)

example (U : X.affineOpens) : preU (𝟙 X) U = U := rfl

end GlobalTheory.AbCoh
