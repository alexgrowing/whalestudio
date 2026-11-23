import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2
namespace RingPf

variable {q : ℕ} {E : Spc}

theorem cast_heq {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) : HEq (x.cast hn hi) x := by
  subst hn hi; rfl

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem cast_zero {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn hi; rfl

theorem cast_add {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn hi; rfl

theorem cup_cast_left {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (a.cast h1 h2) b = (cup q a b).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (b.cast h1 h2) = (cup q a b).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn hi; rfl

abbrev A (q : ℕ) (E : Spc) (k : ℕ) : Type 1 := Ht q E (2 * (k : ℤ)) (k : ℤ)

def gmul {k l : ℕ} (a : A q E k) (b : A q E l) : A q E (k + l) :=
  (cup q a b).cast (by push_cast; ring) (by push_cast; ring)

def gone (q : ℕ) (E : Spc) : A q E 0 := (one q E).cast (by simp) (by simp)

instance : GradedMonoid.GMul (A q E) := ⟨gmul⟩
instance : GradedMonoid.GOne (A q E) := ⟨gone q E⟩

theorem negOnePow_even (i j : ℕ) : (2 * (i : ℤ) * (2 * (j : ℤ))).negOnePow = 1 :=
  Int.negOnePow_even _ ⟨2 * i * j, by ring⟩

section
variable (hr : DivisorRingCompatibility) [NeZero q]
include hr

theorem one_cup (h : Inv q E) {n i : ℤ} (a : Ht q E n i) : cup q (one q E) a = a.cast (by ring) (by ring) :=
  (hr q E).1 h a

theorem cup_one (h : Inv q E) {n i : ℤ} (a : Ht q E n i) : cup q a (one q E) = a.cast (by ring) (by ring) := by
  rw [(hr q E).2.2 a (one q E), (hr q E).1 h, cast_cast]
  simp

theorem gmul_assoc {i j k : ℕ} (a : A q E i) (b : A q E j) (c : A q E k) :
    HEq (gmul (gmul a b) c) (gmul a (gmul b c)) := by
  simp only [gmul, cup_cast_left, cup_cast_right, cast_cast]
  rw [(hr q E).2.1 a b c, cast_cast]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _).symm

theorem gmul_comm {i j : ℕ} (a : A q E i) (b : A q E j) : HEq (gmul a b) (gmul b a) := by
  simp only [gmul]
  rw [(hr q E).2.2 a b, negOnePow_even, one_smul, cast_cast]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _).symm

def gcr (h : Inv q E) : DirectSum.GCommRing (A q E) where
  mul a b := gmul a b
  one := gone q E
  one_mul := by
    rintro ⟨k, a⟩
    refine Sigma.ext (zero_add k) ?_
    show HEq (gmul (gone q E) a) a
    simp only [gmul, gone, cup_cast_left]
    rw [one_cup hr h]
    simp only [cast_cast]
    exact cast_heq _ _ _
  mul_one := by
    rintro ⟨k, a⟩
    refine Sigma.ext (add_zero k) ?_
    show HEq (gmul a (gone q E)) a
    simp only [gmul, gone, cup_cast_right]
    rw [cup_one hr h]
    simp only [cast_cast]
    exact cast_heq _ _ _
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    exact Sigma.ext (add_assoc i j k) (gmul_assoc hr a b c)
  mul_comm := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    exact Sigma.ext (add_comm i j) (gmul_comm hr a b)
  mul_zero a := by simp only [gmul, map_zero, cast_zero]
  zero_mul b := by simp only [gmul, map_zero, AddMonoidHom.zero_apply, cast_zero]
  mul_add a b c := by simp only [gmul, map_add, cast_add]
  add_mul a b c := by simp only [gmul, map_add, AddMonoidHom.add_apply, cast_add]
  natCast n := n • gone q E
  natCast_zero := zero_smul _ _
  natCast_succ n := succ_nsmul _ _
  intCast n := n • gone q E
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc_ofNat n := by
    show Int.negSucc n • gone q E = -((n + 1 : ℕ) • gone q E)
    rw [negSucc_zsmul]

end

section
variable (hn : DivisorNaturality) (hr : DivisorRingCompatibility) [NeZero q]

abbrev ringOf (hr : DivisorRingCompatibility) (E : Spc) (h : Inv q E) : CommRing (DirectSum ℕ (A q E)) :=
  letI := gcr hr h; DirectSum.commRing (A q E)

def projOf (E : Spc) (k : ℕ) : DirectSum ℕ (A q E) →+ A q E k where
  toFun r := r k
  map_zero' := rfl
  map_add' x y := DirectSum.add_apply x y k

include hn in

def mapOf {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') :
    letI := ringOf hr E h; letI := ringOf hr E' h'; DirectSum ℕ (A q E') →+* DirectSum ℕ (A q E) :=
  letI := gcr hr h; letI := gcr hr h'
  DirectSum.toSemiring (fun k => (DirectSum.of (A q E) k).comp (pull (ZMod q) f (tw q k) (2 * (k : ℤ))))
    (by
      show DirectSum.of (A q E) 0 (pull (ZMod q) f (tw q ((0 : ℕ) : ℤ)) (2 * ((0 : ℕ) : ℤ)) (gone q E')) = 1
      rw [gone, pull_cast, (hn q).2.1 f h']
      rfl)
    (by
      intro i j a b
      simp only [AddMonoidHom.comp_apply]
      rw [DirectSum.of_mul_of]
      congr 1
      show pull (ZMod q) f _ _ (gmul a b) = gmul _ _
      simp only [gmul, pull_cast, (hn q).1 f])

include hn in
theorem mapOf_of {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (a : A q E' k) :
    mapOf hn hr f h h' (DirectSum.of (A q E') k a) = DirectSum.of (A q E) k (pull (ZMod q) f (tw q k) (2 * (k : ℤ)) a) := by
  letI := gcr hr h; letI := gcr hr h'
  exact DirectSum.toSemiring_of _ _ _ k a

end

end RingPf

open RingPf in
theorem etale_even_cohomology_graded_commRing_of_cup_ring_axioms (hn : DivisorNaturality) (hr : DivisorRingCompatibility) : LeafRing := by
  intro q _
  exact ⟨{
    R := fun E _ => DirectSum ℕ (A q E)
    ring := fun E h => ringOf hr E h
    ι := fun {E} _ k => DirectSum.of (A q E) k
    π := fun {E} _ k => projOf E k
    map := fun f h h' => mapOf hn hr f h h'
    π_ι := fun {E} _ k a => by
      show (DirectSum.of (A q E) k a) k = a
      exact DirectSum.of_eq_same (β := A q E) k a
    ι_one := fun {E} _ => rfl
    ι_mul := fun {E} h k l a b => by
      letI := gcr hr h
      exact (DirectSum.of_mul_of (A := A q E) a b).symm
    ι_cpow := fun {E} h k x => by
      letI := gcr hr h
      induction k with
      | zero => rw [pow_zero, cpow_zero]; rfl
      | succ k ih =>
        rw [pow_succ, ← ih, cpow_succ]
        show _ = DirectSum.of (A q E) k _ * DirectSum.of (A q E) 1 _
        rw [DirectSum.of_mul_of]
        congr 1
    map_ι := fun {E E'} f h h' k a => by
      exact mapOf_of hn hr f h h' k a
    π_map := fun {E E'} f h h' k r => by
      letI := gcr hr h; letI := gcr hr h'
      induction r using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | of j a =>
        show projOf E k (mapOf hn hr f h h' (DirectSum.of (A q E') j a)) = _
        rw [mapOf_of]
        show (DirectSum.of (A q E) j (pull (ZMod q) f _ _ a)) k = pull (ZMod q) f _ _ ((DirectSum.of (A q E') j a) k)
        by_cases hjk : j = k
        · subst hjk; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), map_zero]
      | add x y hx hy => simp only [map_add, hx, hy] }⟩

theorem LeafRing_of (hn : LeafA6nat) (hr : LeafA6ring) : LeafRing := etale_even_cohomology_graded_commRing_of_cup_ring_axioms hn hr

end LateralTheory.E.D2
