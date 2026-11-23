import Development.EtaleCohomology.EtaleSheaves.LeafKumCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwistPf

def LeafLoc : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LeafTwSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Prim q B → ∀ i j : ℤ,
  ∃ e : ∀ U : Scheme.{0}, (U ⟶ Spec (CommRingCat.of B)) → (Sec (tw q i) U ≃ₗ[ULift.{1} (ZMod q)] Sec (tw q j) U),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ Spec (CommRingCat.of B)) (s : Sec (tw q i) U),
      e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)

theorem LeafTwist_of (hL : LeafLoc) (hT : LeafTwSec) : LateralTheory.E.LeafKumCut.LeafTwist := by
  intro hy q _ B _ hP n i j
  obtain ⟨ζ⟩ := hP
  obtain ⟨e, he⟩ := hT q B ζ i j
  exact hL hy (ZMod q) (Spec (CommRingCat.of B)) (tw q i) (tw q j) e he n

end LateralTheory.E.LeafTwistPf
