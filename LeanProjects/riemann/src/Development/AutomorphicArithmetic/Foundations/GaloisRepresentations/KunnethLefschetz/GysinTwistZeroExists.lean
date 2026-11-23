import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

section Tw
variable {k : Type} [Field k]

private theorem twMul_add (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w)
    (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) (a b : Ht q (sch.obj X) n j) :
    twMul q p hw v n (a + b) = twMul q p hw v n a + twMul q p hw v n b := by
  simp only [twMul, map_add, cast_add]

private def twHom (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w)
    (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) : Ht q (sch.obj X) n j →+ Ht q (sch.obj X) n w :=
  AddMonoidHom.mk' (twMul q p hw v n) (twMul_add q p hw v n)

private theorem twMul_pull (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S k)
    {i j w : ℤ} (hw : i + j = w) (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) (a : Ht q (sch.obj X) n j) :
    pull _ (sch.map f) _ n (twMul q p hw v n a) = twMul q (f ≫ p) hw v n (pull _ (sch.map f) _ n a) := by
  simp only [twMul, pull_cast, (h6 q).1, Functor.map_comp, pull_comp]

private theorem twMul_red (h11 : A11) (Q q : ℕ) [NeZero Q] (hd : q ∣ Q) {X : Scheme.{0}} (p : X ⟶ S k)
    {i j w : ℤ} (hw : i + j = w) (v : Ht Q (sch.obj (S k)) 0 i) (n : ℤ) (a : Ht Q (sch.obj X) n j) :
    red Q q (sch.obj X) n w (twMul Q p hw v n a) =
      twMul q p hw (red Q q _ 0 i v) n (red Q q _ n j a) := by
  simp only [twMul, red_cast, ((h11 Q q hd (sch.obj X)).1), ← pull_red]

private theorem twMul_cup (h6 : DivisorRingCompatibility) (q : ℕ) [NeZero q] {Z : Scheme.{0}} (p : Z ⟶ S k) {n m r i : ℤ}
    (h1 : n + m = r) (hi : 0 + i = i) (v : Ht q (sch.obj (S k)) 0 i) (c : Ht q (sch.obj Z) n 0)
    (b : Ht q (sch.obj Z) m 0) :
    twMul q p (add_zero i) v r (Ht.cast h1 (add_zero 0) (cup q c b)) =
      Ht.cast h1 hi (cup q c (twMul q p (add_zero i) v m b)) := by
  have hc : ∀ {a b a' b' : ℤ} (h : a = a') (h' : b = b') (x : Ht q (sch.obj Z) a b),
      HEq (Ht.cast h h' x) x := by
    intro a b a' b' h h' x
    subst h
    subst h'
    rfl
  simp only [twMul, cup_cast_right]
  generalize (pull (ZMod q) (sch.map p) (tw q i) 0) v = v'
  apply eq_of_heq
  refine (hc _ _ _).trans ?_
  refine HEq.trans ?_ (hc _ _ _).symm
  refine (hc _ _ _).trans ?_
  refine HEq.trans ?_ (hc _ _ _).symm
  have hA := (h6 q (sch.obj Z)).2.1 v' c b
  have hC := (h6 q (sch.obj Z)).2.2 v' c
  have hA2 := (h6 q (sch.obj Z)).2.1 c v' b
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hC
  have e1 : HEq (cup q v' (cup q c b)) (cup q (cup q v' c) b) := by
    rw [hA]
    exact (hc _ _ _).symm
  have e2 : HEq (cup q (cup q v' c) b) (cup q (cup q c v') b) := by
    rw [hC, cup_cast_left]
    exact hc _ _ _
  have e3 : HEq (cup q (cup q c v') b) (cup q c (cup q v' b)) := by
    rw [hA2]
    exact hc _ _ _
  exact e1.trans (e2.trans e3)

private def gZ {l : ℕ} (GT : GysT k) (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i)) (j : ℕ) {d e : ℕ}
    {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m) :
    Ht (l ^ j) (sch.obj Z) n 0 →+ Ht (l ^ j) (sch.obj X) m 0 :=
  (GT.g (l ^ j) h hn (neg_add_cancel (d : ℤ))).comp (twHom (l ^ j) (ι ≫ p) (add_zero (-(d : ℤ))) (w d j) n)

private theorem gZ_apply {l : ℕ} (GT : GysT k) (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i)) (j : ℕ)
    {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (a : Ht (l ^ j) (sch.obj Z) n 0) :
    gZ GT w j h hn a = GT.g (l ^ j) h hn (neg_add_cancel (d : ℤ))
      (twMul (l ^ j) (ι ≫ p) (add_zero (-(d : ℤ))) (w d j) n a) := rfl

private def mkGys0 (hIn : In) {l : ℕ} [Fact l.Prime] (GT : GysT k) (hu : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k))
    (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i))
    (hw : ∀ (i : ℤ) (j : ℕ), red (l ^ (j + 1)) (l ^ j) _ 0 (-i) (w i (j + 1)) = w i j)
    (hb : ∀ (i : ℤ) (j : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (n : ℤ),
      Function.Bijective (twMul (l ^ j) p (add_zero (-i)) (w i j) n)) : Gys0 k l where
  g j _ _ _ _ _ _ h _ _ hn := gZ GT w j h hn
  exact := by
    intro j d e Z X p ι h n m hn U hU y
    have E := GT.exact (l ^ j) (hu j) h hn (neg_add_cancel (d : ℤ)) U hU
    rw [E y]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (hb d j (ι ≫ p) n).2 a
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, rfl⟩
  inj := by
    intro j d e Z X p ι h n m hn U hU hs
    exact (GT.inj (l ^ j) (hu j) h hn (neg_add_cancel (d : ℤ)) U hU hs).comp (hb d j (ι ≫ p) n).1
  nat := by
    intro j d e' e Z' X' Z X p' ι' p ι h' h f t hfp hpb n m hn a
    have hc : t ≫ ι ≫ p = ι' ≫ p' := by
      rw [← Category.assoc, ← hpb.w, Category.assoc, hfp]
    rw [gZ_apply, gZ_apply, GT.nat (l ^ j) (hu j) h' h f t hpb hn _ _, twMul_pull hIn.a6nat _ t (ι ≫ p), hc]
  proj := by
    intro j d e Z X p ι h n m r s t h1 h2 h3 h4 a b
    rw [gZ_apply, gZ_apply]
    unfold cup0
    rw [twMul_cup hIn.a6ring _ _ h1 (zero_add _)]
    exact GT.proj (l ^ j) (hu j) h h1 h2 h3 h4 (zero_add _) (neg_add_cancel _) (neg_add_cancel _) (add_zero 0) a _
  red := by
    intro j d e Z X p ι h n m hn a
    rw [gZ_apply, gZ_apply, GT.red (l ^ (j + 1)) (l ^ j) (hu _) (dvd_succ l j) h hn _ _,
      twMul_red hIn.a11 _ _ (dvd_succ l j), hw]

end Tw

theorem gysinTwistZero_exists : GysinCondition := by
  intro hI hB l _ k _ _ hl hT hG
  obtain ⟨GT⟩ := hG
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  choose u v huv using hT
  have hu : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := by
    intro j
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hl).pow j
  refine ⟨mkGys0 hI GT hu (fun i j => (v i).1 j) (fun i j => (v i).2 j) ?_⟩
  intro i j X p n
  exact (hB hI k (l ^ j) (hu j) i ((u i).1 j) ((v i).1 j) (huv i j) p n 0 (-i)).1 (add_zero (-i))

end UpperTheory.Gal.KunnethLefschetz
