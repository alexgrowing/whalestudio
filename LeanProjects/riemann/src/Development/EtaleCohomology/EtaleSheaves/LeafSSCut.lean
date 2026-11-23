import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSSCut

def incl0 {R : Type} [CommRing R] (K : Cx R) [K.IsStrictlyLE 0] :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (K.X 0) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) (fun k _ =>
    (CochainComplex.isZero_of_isStrictlyLE K 0 k (by
      have : (0 : ℤ) + 1 = k := by assumption
      omega)).eq_of_tgt _ _)

instance chains_isStrictlyLE {R : Type} [CommRing R] (E : Spc) : CochainComplex.IsStrictlyLE ((chains R).obj E) 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

def LeafFilt : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (K : Cx R) [K.IsStrictlyLE 0] (F : Shv R) (n : ℤ),
  (∀ r : ℕ, 0 < r → (r : ℤ) ≤ n →
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (K.X (-(r : ℤ)))) F (n - r))) →
  Finite (HK.pull R (incl0 K) F n).ker

def LeafCompare : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ),
  Eqv R (cechAug f) F → Finite (HK.pull R (incl0 ((chains R).obj (cech f))) F n).ker →
  Finite (pull R (sch.map f) F n).ker

def LeafTerms : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f]
  (r : ℕ) (m : ℤ), (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → Finite (H R (sch.obj Z) F m)) →
  Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (cech f)).X (-(r : ℤ)))) F m)

theorem goal_of (h1 : LeafFilt) (h2 : LeafCompare) (h3 : LeafTerms) : E4.LeafSS := by
  intro hy R _ F Y X f _ n hE hfin
  refine h2 hy R F f n hE ?_
  refine h1 hy R ((chains R).obj (cech f)) F n ?_
  intro r hr hrn
  exact h3 hy R F f r (n - r) (fun Z g hg => hfin Z g hg (n - r) (by omega))

end LateralTheory.E.LeafSSCut
