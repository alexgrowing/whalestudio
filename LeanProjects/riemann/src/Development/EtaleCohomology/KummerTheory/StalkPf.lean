import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

theorem stalk_neg (h9 : A9) (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
    (A : CommRingCat.{0}) (s : R ⟶ A) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ)
    (n : ℤ) (hn : n < 0) : IsoUpTo N (lh q p (Spec.map s) i r c M n) := by
  have : Subsingleton (Ht q (sch.obj (pullback p (Spec.map s))) n i) := (h9 (ZMod q) (tw q i)).1 _ n hn
  haveI : ∀ a : Fin (M + 1), Subsingleton (Ht q (sch.obj (Spec A)) (n - ((a : ℕ) : ℤ)) 0) :=
    fun a => (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  refine ⟨fun y _ => ?_, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  funext a t
  exact Subsingleton.elim _ _

def ExtOne : Prop := DivisorNaturality → DivisorRingCompatibility → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R A : CommRingCat.{0}} (p : X ⟶ Spec R)
  (s : R ⟶ A), IsUnit (q : A) → ∀ (a i : ℤ) (x : Ht q (sch.obj X) a i) (t : ZMod q),
    ext q p (Spec.map s) a a i x ((t • one q (sch.obj (Spec A))).cast (by ring) rfl) =
      t • pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ x

def StalkTop : Prop := DivisorNaturality → DivisorRingCompatibility → A9 → B2 → H0 → ExtOne → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}}
  {R : CommRingCat.{0}} (p : X ⟶ Spec R) (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ), Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i) →
  (∀ a ≤ M, IsoUpTo N (comb q (c a))) → ∀ n : ℤ, 0 ≤ n → n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)

theorem inv_sch (q : ℕ) {X : Scheme.{0}} (hq : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U ⟨g⟩
  have g' : U ⟶ X := g
  simpa using hq.map g'.appTop.hom

theorem unit_spec (q : ℕ) {A : CommRingCat.{0}} (hq : IsUnit (q : A)) : IsUnit (q : Γ(Spec A, ⊤)) := by
  simpa using hq.map (Scheme.ΓSpecIso A).inv.hom

theorem pull_zsmul {E E' : Spc} (f : E ⟶ E') (q : ℕ) [NeZero q] {n i : ℤ} (t : ZMod q) (x : Ht q E' n i) :
    pull _ f _ _ (t • x) = t • pull _ f _ _ x := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem cast_cast' (q : ℕ) {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem pull_cast (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast h1 h2) = Ht.cast h1 h2 (pull _ f _ _ x : Ht q E n i) := by
  subst h1 h2; rfl

theorem cast_smul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (t : ZMod q) (x : Ht q E n i) :
    (t • x).cast h1 h2 = t • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem cup_cast_r (q : ℕ) {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (y : Ht q E m j) : cup q a (y.cast h1 h2) = (cup q a y).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_smul_r (q : ℕ) [NeZero q] {E : Spc} {n m i j : ℤ} (t : ZMod q) (a : Ht q E n i) (y : Ht q E m j) :
    cup q a (t • y) = t • cup q a y := by
  rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem unit_map (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : IsUnit (q : Γ(Y, ⊤)) := by
  simpa using hq.map f.appTop.hom

theorem extOne_pf : ExtOne := by
  intro h6n h6r q _ X R A p s hq a i x t
  have hI := inv_sch q (unit_spec q hq)
  have hP := inv_sch q (unit_map q (pullback.snd p (Spec.map s)) (unit_spec q hq))
  unfold ext
  rw [pull_cast, pull_zsmul, (h6n q).2.1 _ hI, cup_cast_r, cup_smul_r, (h6r q _).2.2, (h6r q _).1 hP]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_smul', cast_cast']
  rfl

theorem cast_zero' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    (0 : Ht q E n i).cast h1 h2 = 0 := by
  subst h1 h2; rfl

theorem cast_nsmul' (q : ℕ) {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (N : ℕ) (x : Ht q E n i) :
    (N • x).cast h1 h2 = N • x.cast h1 h2 := by
  subst h1 h2; rfl

theorem ext_zero (q : ℕ) [NeZero q] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i) :
    ext q pX pY a n i x 0 = 0 := by
  unfold ext; rw [map_zero, map_zero, cast_zero']

theorem stalkTop_pf : StalkTop := by
  intro h6n h6r h9 hb2 h0 hE q _ X R p A s hA hq i r c M N he hc n hn0 hnM
  lift n to ℕ using hn0
  have hnM' : n ≤ M := by exact_mod_cast hnM
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  let a : Fin (M + 1) := ⟨n, by omega⟩
  have hsub : ∀ b : Fin (M + 1), b ≠ a → Subsingleton (Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0) := by
    intro b hb
    have hb' : (b : ℕ) ≠ n := fun h => hb (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hb' with h | h
    · exact hb2 (ZMod q) A hA (tw q 0) _ (by omega)
    · exact (h9 (ZMod q) (tw q 0)).1 _ _ (by omega)
  have hH := h0 h9 q A hA hqA
  have hex : ∀ z : Ht q (sch.obj (Spec A)) ((n : ℤ) - (n : ℤ)) 0, ∃ t : ZMod q,
      z = (t • one q (sch.obj (Spec A))).cast (by ring) rfl := by
    intro z
    obtain ⟨t, ht⟩ := hH.2 (z.cast (by ring) rfl)
    refine ⟨t, ?_⟩
    rw [show t • one q (sch.obj (Spec A)) = _ from ht, cast_cast']; rfl
  have hform : ∀ (y : ∀ b : Fin (M + 1), Fin (r b) → Ht q (sch.obj (Spec A)) ((n : ℤ) - ((b : ℕ) : ℤ)) 0)
      (t : Fin (r n) → ZMod q), (∀ u, y a u = (t u • one q (sch.obj (Spec A))).cast (by ring) rfl) →
      lh q p (Spec.map s) i r c M n y = pull _ (sch.map (pullback.fst p (Spec.map s))) _ _ (comb q (c n) t) := by
    intro y t hy
    unfold lh comb
    rw [Fintype.sum_eq_single a]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hy u, pull_zsmul]
      exact hE h6n h6r q p s hqA n i (c n u) (t u)
    · intro b hb
      haveI := hsub b hb
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [Subsingleton.elim (y b u) 0, ext_zero]
  have hbij := he (n : ℤ)
  refine ⟨fun y hy0 => ?_, fun b => ?_⟩
  · choose t ht using fun u => hex (y a u)
    rw [hform y t ht] at hy0
    have hc0 : comb q (c n) t = 0 := hbij.1 (by rw [hy0, map_zero])
    have hNt := (hc n hnM').1 t hc0
    funext b u
    by_cases hb : b = a
    · subst hb
      show N • y a u = 0
      rw [ht u]
      have e1 : N • t u = 0 := by simpa using congrFun hNt u
      rw [← cast_nsmul', ← smul_assoc, e1, zero_smul, cast_zero']
    · haveI := hsub b hb
      exact Subsingleton.elim _ _
  · obtain ⟨w, rfl⟩ := hbij.2 b
    obtain ⟨t, ht⟩ := (hc n hnM').2 w
    refine ⟨Pi.single a (fun u => (t u • one q (sch.obj (Spec A))).cast (by ring) rfl), ?_⟩
    rw [hform _ t (fun u => by rw [Pi.single_eq_same]), ht, map_nsmul]

theorem Stalk_of (h0 : H0) : Stalk := by
  intro h6n h6r h9 hb2 q _ X R p A s hA hq i r c M N he hc n hn
  by_cases hneg : n < 0
  · exact stalk_neg h9 q p A s i r c M N n hneg
  · exact stalkTop_pf h6n h6r h9 hb2 h0 extOne_pf q p A s hA hq i r c M N he hc n (by omega) hn
