import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.FinalOdd
import Mathlib

open UpperTheory.V.KL

namespace PositivityTheory.KB

theorem lev_zk (l n : ℕ) : ∀ t, UpperTheory.V.ZK.lev l n t = lev l n t
  | 0 => rfl
  | t + 1 => congrArg (l * ·) (lev_zk l n t)

private theorem step_heq (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) (m c : ℕ) {a b : ℕ} (e : a = b)
    (u : grpH (GL (Fin a) R) m) (v : grpH (GL (Fin b) R) m) (h : HEq u v) :
    HEq ((grpHMap (UpperTheory.V.ZK.psi R l a) m).hom u -
        c • (grpHMap (stab R a (l * a) (Nat.le_mul_of_pos_left _ hl)) m).hom u)
      ((grpHMap (psi R l b) m).hom v - c • (grpHMap (stab R b (l * b) (Nat.le_mul_of_pos_left _ hl)) m).hom v) := by
  subst e
  obtain rfl := eq_of_heq h
  rfl

theorem zSeq_zk (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (x : grpH (GL (Fin n) R) m) :
    ∀ t, HEq (UpperTheory.V.ZK.zSeq R hl x t) (zSeq R hl x t)
  | 0 => HEq.rfl
  | t + 1 => step_heq R hl m (l ^ (t + 2)) (lev_zk l n t) _ _ (zSeq_zk R hl x t)

private theorem rank_heq (R : Type) [CommRing R] (m : ℕ) {X : Type} {a b : ℕ} (e : a = b)
    (f : X → grpH (GL (Fin a) R) m) (g : X → grpH (GL (Fin b) R) m) (h : ∀ x, HEq (f x) (g x)) :
    Module.rank ℤ (Submodule.span ℤ (Set.range f)) = Module.rank ℤ (Submodule.span ℤ (Set.range g)) := by
  subst e
  obtain rfl : f = g := funext fun x => eq_of_heq (h x)
  rfl

theorem bOdd_zk : UpperTheory.V.ZK.BOdd := fun L _ _ hL k hk hr l hl n hn =>
  (rank_heq _ _ (lev_zk l n k) _ _ fun x => zSeq_zk _ hl x k).le.trans (bStarOdd L hL k hk hr l hl n hn)

end PositivityTheory.KB
