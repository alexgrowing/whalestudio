import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentVarUnit (A : Type) [CommRing A] : (LaurentPolynomial A)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

def laurentVar (A : Type) [CommRing A] : (Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom (laurentVarUnit A)

namespace GmPhi

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

end GmPhi

def gmPhi (q : ℕ) (A : Type) [CommRing A] (i : ℤ) : Ht q (sp A) 0 (i - 1) →+ Ht q (sp (LaurentPolynomial A)) 1 i where
  toFun a := (cup q (pull _ (spMap (LaurentPolynomial.C : A →+* LaurentPolynomial A)) (tw q (i - 1)) 0 a)
    (kum q (laurentVar A))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add, AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC

end
