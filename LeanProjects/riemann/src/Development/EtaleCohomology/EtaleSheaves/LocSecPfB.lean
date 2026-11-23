import Development.EtaleCohomology.EtaleSheaves.LocSecPfA

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfB

def HomSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ∃ e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X,
    ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)

def ClassSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0})
  (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X),
  (∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)) →
  ∀ (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem locSecB_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LocSecPf.LocSecB := by
  intro R _ X F n
  obtain ⟨e, he⟩ := h1 R X
  exact h2 R X e he F n

theorem LocSec_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPf.LocSec_of LateralTheory.E.LocSecPfA.locSecA (locSecB_of h1 h2)

end LateralTheory.E.LocSecPfB
