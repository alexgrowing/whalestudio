import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.SimplexFace

noncomputable section

open CategoryTheory UpperTheory.V.KL

namespace UpperTheory.V.Published

def KPlusExists : Prop := ∀ (R : Type) [CommRing R], Nonempty (Plus R)

def KAcyclicHomology : Prop :=
  ∀ (S : SSet.{0}) (Y : TopCat.{0}) (f : SSet.toTop.obj S ⟶ Y) (x : SSet.toTop.obj S), PathConnectedSpace (SSet.toTop.obj S) →
    IsConnCW Y → IsAcyclicSpace (hoFib f (f x)) → ∀ n : ℕ, IsIso (singHMap f n)

def KMilnor : Prop := ∀ (S : SSet.{0}) (n : ℕ), IsIso (SSet.homologyMap (sSetTopAdj.unit.app S) ZZ n)

def KHurewicz : Prop :=
  ∀ (R : Type) [CommRing R] (M : Plus R) (k : ℕ) (h : Additive (M.K (k + 2)) →+ singH M.X (k + 2)),
    IsHurewicz M.X M.pt (k + 2) (fun a => h (Additive.ofMul a)) → ∀ x, h x = 0 → arlR (k + 2) • x = 0

def KStability : Prop :=
  ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i n : ℕ, 2 * i + s + 2 ≤ n →
    IsIso (grpHMap (stab R n (n + 1) (Nat.le_succ n)) i)

end UpperTheory.V.Published

end
