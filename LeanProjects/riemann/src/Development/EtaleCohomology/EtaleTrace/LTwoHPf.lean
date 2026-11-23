import Development.EtaleCohomology.EtaleTrace.LCoprodInjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LTwoCover : Prop := ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → Cover2 R (sch.map i) (sch.map j)

def LTwoOverlap : Prop := ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → ∀ (F : Shv R) (n : ℤ), Subsingleton (H R (pullback (sch.map i) (sch.map j)) F n)

def LTwoMV : Prop := Base → ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (F : Shv R), (∀ m : ℤ, Subsingleton (H R (pullback f g) F m)) →
  ∀ (n : ℤ) (x : H R E F n), pull R f F n x = 0 → pull R g F n x = 0 → x = 0

def LTwoEpi : Prop := ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → ∀ n, Epi (biprod.desc ((free R).map ((sch.map i).app n)) ((free R).map ((sch.map j).app n)))

instance : PreservesLimitsOfSize.{0, 0} (disc : PSh ⥤ Spc) := by
  unfold disc SimplicialObject.const
  infer_instance

instance : PreservesLimitsOfSize.{0, 0} (sch : Scheme.{0} ⥤ Spc) := by
  unfold sch
  infer_instance

end LateralTheory.EtaleTrace
