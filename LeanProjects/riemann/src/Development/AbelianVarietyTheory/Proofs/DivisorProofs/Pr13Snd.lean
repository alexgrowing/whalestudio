import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

noncomputable section

namespace GlobalTheory.Et.CovChar.Trip

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev Tr : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Tr f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    simp only [Category.assoc]
    rw [pullback.condition (f := f) (g := f), pullback.condition_assoc, pullback.condition (f := f) (g := f)])

@[reassoc (attr := simp)] theorem pr13_fst : pr13 f ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pr13_snd : pr13 f ≫ pullback.snd f f = pullback.snd _ _ ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

variable (R : Type) [CommRing R]

def d1 : (freeOn R).obj (pullback f f) ⟶ (freeOn R).obj Y :=
  (freeOn R).map (pullback.snd f f) - (freeOn R).map (pullback.fst f f)

def d2 : (freeOn R).obj (Tr f) ⟶ (freeOn R).obj (pullback f f) :=
  (freeOn R).map (pullback.snd _ _) - (freeOn R).map (pr13 f) + (freeOn R).map (pullback.fst _ _)

theorem d2_comp : d2 f R ≫ d1 f R = 0 := by
  simp only [d1, d2, Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_sub, ← Functor.map_comp,
    pr13_fst, pr13_snd, pullback.condition]
  abel

end GlobalTheory.Et.CovChar.Trip
