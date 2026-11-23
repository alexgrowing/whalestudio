import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_bij (q : ℕ) {A B : Spc} (f : A ⟶ B) [IsIso f] (n i : ℤ) :
    Function.Bijective (fun x : Ht q B n i => (pull _ f _ _ x : Ht q A n i)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => pull _ (inv f) _ _ y, fun x => ?_, fun y => ?_⟩
  · show pull _ (inv f) _ _ (pull _ f _ _ x) = x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · show pull _ f _ _ (pull _ (inv f) _ _ y) = y
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem pull_cup (q : ℕ) {A B : Spc} (f : A ⟶ B) {n m i j : ℤ} (a : Ht q B n i) (b : Ht q B m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem pull_cast' (q : ℕ) {A B : Spc} (f : A ⟶ B) {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q B n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q A n i) := by
  subst hn; subst hi; rfl

theorem UpperTheory.lerayHirsch_of_iso_square :
    ∀ (q : ℕ) [NeZero q] {X X' E E' : Spc} (π : X ⟶ E) (π' : X' ⟶ E') (u : X' ⟶ X) (b : E' ⟶ E) [IsIso u] [IsIso b], u ≫ π = π' ≫ b →
        ∀ {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)), LH q π d e c → LH q π' d e (fun j => pull _ u _ _ (c j)) := by
  intro q _ X X' E E' π π' u b _ _ w m d e c h n i
  have hP : Function.Bijective (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
      (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) :=
    ⟨fun a a' haa => funext fun j => (pull_bij q b _ _).1 (congrFun haa j),
      fun y => ⟨fun j => ((pull_bij q b _ _).2 (y j)).choose,
        funext fun j => ((pull_bij q b _ _).2 (y j)).choose_spec⟩⟩
  have hc : ∀ a : ∀ j, Ht q E (n - d j) (i - e j),
      (∑ j, ((cup q (pull _ π' _ _ (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) (pull _ u _ _ (c j))).cast
        (by ring) (by ring) : Ht q X' n i)) =
      pull _ u _ _ (∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast', pull_cup, ← pull_comp, ← pull_comp, w]
  have hcomp := (pull_bij q u n i).comp (h n i)
  have heq : (fun y : ∀ j, Ht q E' (n - d j) (i - e j) =>
      ∑ j, ((cup q (pull _ π' _ _ (y j)) (pull _ u _ _ (c j))).cast (by ring) (by ring) : Ht q X' n i)) ∘
      (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
        (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) =
      (fun x : Ht q X n i => (pull _ u _ _ x : Ht q X' n i)) ∘ (fun a : ∀ j, Ht q E (n - d j) (i - e j) =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) :=
    funext hc
  rw [← heq] at hcomp
  exact (Function.Bijective.of_comp_iff _ hP).1 hcomp
