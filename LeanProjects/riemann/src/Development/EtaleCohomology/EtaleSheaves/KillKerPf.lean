import Development.EtaleCohomology.EtaleSheaves.KerLocPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.KerLocPf

namespace LateralTheory.E.KillKerPf

def KillAt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n, pull _ (sch.map (Spec.map φ')) (tw q i) n x = 0 →
  ∀ r : Ideal D, r.IsPrime → ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
    (∃ Q : Ideal E, Q.IsPrime ∧ Q.comap e.hom = r) ∧ pull _ (sch.map (Spec.map e)) (tw q i) n x = 0

def EtGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i n : ℤ) (D : CommRingCat.{0})
  (x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n),
  (∀ r : Ideal D, r.IsPrime → ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
    (∃ Q : Ideal E, Q.IsPrime ∧ Q.comap e.hom = r) ∧ pull _ (sch.map (Spec.map e)) (tw q i) n x = 0) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧ SpS e ∧ pull _ (sch.map (Spec.map e)) (tw q i) n x = 0

end LateralTheory.E.KillKerPf
