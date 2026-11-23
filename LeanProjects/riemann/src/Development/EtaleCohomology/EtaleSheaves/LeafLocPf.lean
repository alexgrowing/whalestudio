import Development.EtaleCohomology.EtaleSheaves.LeafTwistPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocPf

def overIso {R : Type} [CommRing R] (X : Scheme.{0}) (F G : Shv R)
    (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U))
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) :
    F.over X ≅ G.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun Y => (e Y.unop.left Y.unop.hom).toModuleIso) (by
    intro Y Y' f
    ext s
    have h := he f.unop.left Y.unop.hom s
    rw [Over.w f.unop] at h
    exact h))

def LocOver : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

theorem LeafLoc_of (hO : LocOver) : LateralTheory.E.LeafTwistPf.LeafLoc := by
  intro hy R _ X F G e he n
  exact hO hy R X F G ⟨overIso X F G e he⟩ n

abbrev secCx {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) : CochainComplex (ModuleCat.{1} (ULift.{1} R)) ℤ :=
  ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)).mapHomologicalComplex _).obj (res R F)

def LocSec : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ (secCx F X).homology n)

def LocSlice : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty ((secCx F X).homology n ≃+ (secCx G X).homology n)

theorem LocOver_of (hS : LocSec) (hL : LocSlice) : LocOver := by
  intro hy R _ X F G hi n
  obtain ⟨a⟩ := hS hy R X F n
  obtain ⟨b⟩ := hS hy R X G n
  obtain ⟨c⟩ := hL hy R X F G hi n
  exact ⟨(a.trans c).trans b.symm⟩

theorem LeafLoc_of' (hS : LocSec) (hL : LocSlice) : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LeafLoc_of (LocOver_of hS hL)

end LateralTheory.E.LeafLocPf
