import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Tr

def SplitBy {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) {m : ℕ} (s : Fin m → (V ⟶ Z)) : Prop :=
  ∃ hs : ∀ j, s j ≫ f = y, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
    ∐ (fun _ : Fin m => V) ⟶ pullback f y)

def Splits {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) : Prop :=
  ∃ (m : ℕ) (s : Fin m → (V ⟶ Z)), SplitBy f y s

def splitSieve {Z X S : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) : Sieve S :=
  Sieve.generate (fun V (v : V ⟶ S) => Splits f (v ≫ x))

theorem IsTransfer.apply_of_splitBy (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z}
    (ht : IsTransfer R f t) {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)} (hs : SplitBy f y s) :
    (free R).map (yoneda.map y) ≫ t = ∑ j, (free R).map (yoneda.map (s j)) :=
  ht V y m s hs.1 hs.2

end GlobalTheory.EtC.Tr
