import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem ht_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 x) = Ht.cast (h1.trans h3) (h2.trans h4) x := by
  subst h1 h2 h3 h4
  rfl

private theorem ht_cast_self {q : ℕ} {E : Spc} {n i : ℤ} (h1 : n = n) (h2 : i = i) (x : Ht q E n i) : Ht.cast h1 h2 x = x := rfl

private theorem ht_cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast h1 h2 (0 : Ht q E n i) = 0 := by
  subst h1 h2
  rfl

private theorem ht_cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    Ht.cast h1 h2 (x - y) = Ht.cast h1 h2 x - Ht.cast h1 h2 y := by
  subst h1 h2
  rfl

private theorem ht_cast_sum {q : ℕ} {E : Spc} {n i n' i' : ℤ} {ι : Type} (h1 : n = n') (h2 : i = i') (s : Finset ι)
    (f : ι → Ht q E n i) : Ht.cast h1 h2 (∑ j ∈ s, f j) = ∑ j ∈ s, Ht.cast h1 h2 (f j) := by
  subst h1 h2
  rfl

private theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (h : Ht.cast h1 h2 x = 0) : x = 0 := by
  subst h1 h2
  exact h

private theorem cup_cast_left {q : ℕ} {E : Spc} {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E m j) : cup q (Ht.cast h1 h2 x) y = Ht.cast (by rw [h1]) (by rw [h2]) (cup q x y) := by
  subst h1 h2
  rfl

private theorem cup_cast_right {q : ℕ} {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (x : Ht q E n i)
    (y : Ht q E m j) : cup q x (Ht.cast h1 h2 y) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q x y) := by
  subst h1 h2
  rfl

private theorem pull_cast {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_cup {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem cup_one_right {q : ℕ} [NeZero q] {E : Spc} (hE : Inv q E) {n i : ℤ} (a : Ht q E n i) :
    cup q a (one q E) = Ht.cast (by ring) (by ring) a := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q E a (one q E), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a, ht_cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem cup_assoc' {q : ℕ} [NeZero q] {E : Spc} {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l) :
    cup q a (cup q b c) = Ht.cast (by ring) (by ring) (cup q (cup q a b) c) := by
  rw [GlobalTheory.T.tateTwistCupProduct_assoc q E a b c, ht_cast_cast]
  rfl

private theorem step_term {q : ℕ} [NeZero q] {X B : Spc} (p : B ⟶ X) (ξX : Ht q X 2 1) (ξ : Ht q B 2 1) (hX : Inv q X)
    (hrel : ∀ j : ℕ, cpow q ξ (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) ξ).cast (by push_cast; ring) (by push_cast; ring))
    {u v n i : ℤ} (x : Ht q X u v) (j : ℕ) (h1 : u + 2 * ((j + 1 : ℕ) : ℤ) = n) (h2 : v + ((j + 1 : ℕ) : ℤ) = i)
    (h3 : u + 2 * (j : ℤ) + 2 * ((1 : ℕ) : ℤ) = n) (h4 : v + (j : ℤ) + ((1 : ℕ) : ℤ) = i) :
    Ht.cast h1 h2 (cup q (pull _ p _ _ x) (cpow q ξ (j + 1))) =
      Ht.cast h3 h4 (cup q (pull _ p _ _ (cup q x (cpow q ξX j))) (cpow q ξ 1)) := by
  have e0 : cpow q ξ 1 = (cup q (cpow q (pull _ p _ _ ξX) 0) ξ).cast (by simp) (by simp) := hrel 0
  rw [hrel j, e0, cup_cast_right, cup_cast_right, ht_cast_cast, ht_cast_cast, ← UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX j hX,
    ← UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX 0 hX, cup_assoc', cup_assoc', ht_cast_cast, ht_cast_cast, ← pull_cup, ← pull_cup, cpow_zero,
    cup_cast_right, cup_one_right hX, ht_cast_cast, pull_cast, cup_cast_left, ht_cast_cast]

private theorem gysin_injective {q : ℕ} {X B : Spc} (p : B ⟶ X) (ξ : Ht q B 2 1)
    (LHp : LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q ξ j))
    (n i : ℤ) (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1))
    (h : Ht.cast (n' := n) (i' := i) (by simp) (by simp) (cup q (pull _ p _ _ y0) (cpow q ξ 0)) +
      Ht.cast (n' := n) (i' := i) (by push_cast; ring) (by push_cast; ring) (cup q (pull _ p _ _ y1) (cpow q ξ 1)) = 0) :
    y0 = 0 ∧ y1 = 0 := by
  let a' : ∀ j : Fin 2, Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) := fun j =>
    Fin.cases (motive := fun j : Fin 2 => Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
      (Ht.cast (by simp) (by simp) y0)
      (fun k => Ht.cast (by have : (k : ℕ) = 0 := by omega
                            simp [this]) (by have : (k : ℕ) = 0 := by omega
                                             simp [this]) y1) j
  have e0 : a' 0 = Ht.cast (by simp) (by simp) y0 := rfl
  have e1 : a' 1 = Ht.cast (by simp) (by simp) y1 := rfl
  have hz := (LHp n i).1 (a₁ := a') (a₂ := 0) (by
    simp only [Fin.sum_univ_two, Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, add_zero]
    rw [e0, e1, pull_cast, pull_cast, cup_cast_left, cup_cast_left, ht_cast_cast, ht_cast_cast]
    exact h)
  exact ⟨eq_zero_of_cast _ _ _ (e0.symm.trans (congrFun hz 0)), eq_zero_of_cast _ _ _ (e1.symm.trans (congrFun hz 1))⟩

private theorem core {q : ℕ} [NeZero q] (N : ℕ) (hN : 1 ≤ N) {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
    (hc : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (hX : Inv q X) (hY : Inv q Y)
    (LHX : LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j))
    (LHp : LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j))
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    (n i : ℤ) (a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
    (h : ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) = 0) : a = 0 := by
  have pp : ∀ {m k : ℤ} (x : Ht q E m k), (pull _ β _ _ (pull _ πY _ _ x) : Ht q B m k) = pull _ p _ _ (pull _ πX _ _ x) := by
    intro m k x
    rw [← pull_comp, ← pull_comp, hc]
  have h1 : ∑ j : Fin (N + 1), ((cup q (pull _ p _ _ (pull _ πX _ _ (a j))) (cpow q (pull _ β _ _ ξY) j)).cast (by ring) (by ring) : Ht q B n i) = 0 := by
    have h' := congrArg (pull _ β (tw q i) n) h
    rw [map_sum, map_zero] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast, pull_cup, UpperTheory.pull_cupPow_eq_cupPow_pull q β ξY j hY, pp]
  rw [Fin.sum_univ_succ] at h1
  let y0 : Ht q X n i := Ht.cast (by simp) (by simp) (pull _ πX _ _ (a 0))
  let y1 : Ht q X (n - 2) (i - 1) := ∑ k : Fin N, Ht.cast (by simp only [Fin.val_succ]; push_cast; ring) (by simp only [Fin.val_succ]; push_cast; ring)
    (cup q (pull _ πX _ _ (a k.succ)) (cpow q ξX k))
  have hy := gysin_injective p (pull _ β _ _ ξY) LHp n i y0 y1 (by
    rw [← h1]
    congr 1
    · simp only [y0]
      rw [pull_cast, cup_cast_left, ht_cast_cast]
      rfl
    · simp only [y1]
      rw [map_sum, map_sum, AddMonoidHom.finset_sum_apply, ht_cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pull_cast, cup_cast_left, ht_cast_cast]
      exact (step_term p ξX (pull _ β _ _ ξY) hX hrel _ k _ _ _ _).symm)
  have hb := (LHX (n - 2) (i - 1)).1
    (a₁ := fun k => Ht.cast (by simp only [Fin.val_succ]; push_cast; ring) (by simp only [Fin.val_succ]; push_cast; ring) (a k.succ)) (a₂ := 0) (by
      simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, Finset.sum_const_zero]
      rw [← hy.2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pull_cast, cup_cast_left, ht_cast_cast])
  have ha := fun k : Fin N => eq_zero_of_cast _ _ _ (congrFun hb k)
  let k0 : Fin N := ⟨0, hN⟩
  let f : ∀ j : Fin N, Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) := Pi.single k0 (Ht.cast (by simp [k0]) (by simp [k0]) (a 0))
  have hf := (LHX n i).1 (a₁ := f) (a₂ := 0) (by
    simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single k0 (fun j _ hj => by simp only [f, Pi.single_eq_of_ne hj, map_zero, AddMonoidHom.zero_apply, ht_cast_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [f, Pi.single_eq_same]
    have e : cpow q ξX (k0 : ℕ) = (one q X).cast (by simp [k0]) (by simp [k0]) := rfl
    have hy0 : (pull _ πX _ _ (a 0) : Ht q X _ _) = 0 := eq_zero_of_cast _ _ _ hy.1
    rw [e, cup_cast_right, cup_one_right hX, pull_cast, hy0]
    simp only [ht_cast_zero])
  have h0 : a 0 = 0 := eq_zero_of_cast _ _ _ ((Pi.single_eq_same (M := fun j : Fin N => Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) k0 _).symm.trans (congrFun hf k0))
  funext j
  refine Fin.cases h0 ha j

theorem UpperTheory.leray_hirsch_of_pullback_square :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (_ : p ≫ πX = β ≫ πY)
        (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1), Inv q X → Inv q Y →
        LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
        LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j) →
        (∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring)) →
        ∀ n i : ℤ, Function.Injective fun a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) =>
          ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := by
  intro q _ N hN E X Y B πX πY p β hc ξX ξY hX hY LHX LHp hrel n i a b hab
  have hab' : ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) =
      ∑ j, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := hab
  refine sub_eq_zero.1 (core N hN πX πY p β hc ξX ξY hX hY LHX LHp hrel n i (a - b) ?_)
  simp only [Pi.sub_apply, map_sub, AddMonoidHom.sub_apply, ht_cast_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hab'
