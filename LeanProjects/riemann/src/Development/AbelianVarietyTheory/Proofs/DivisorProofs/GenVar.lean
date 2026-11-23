import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.GenericMember

noncomputable def genVar (k : Type) [Field k] (N : ℕ) {X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (i : Fin N) : Γ(X', ⊤) :=
  f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv
    (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))

noncomputable def genSec (k : Type) [Field k] (N : ℕ) {X X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X)
    (b : Fin N → L.Sec) : (L.pull π).Sec :=
  ∑ i, genVar k N f' i • secPull (b i) π

end GlobalTheory.GenericMember
