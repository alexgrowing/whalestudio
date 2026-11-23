import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_cast {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_cup {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

theorem UpperTheory.pull_cupPow_eq_cupPow_pull :
    ∀ (q : ℕ) [NeZero q] {X Y : Spc} (f : X ⟶ Y) (ξ : Ht q Y 2 1) (j : ℕ), Inv q Y → pull _ f _ _ (cpow q ξ j) = cpow q (pull _ f _ _ ξ) j := by
  intro q _ X Y f ξ j hY
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pull_cast, (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.1 f hY]
  | succ k ih =>
    rw [cpow_succ, cpow_succ, pull_cast, pull_cup, ih]
