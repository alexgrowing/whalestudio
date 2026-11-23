import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Gysin

open GlobalTheory.EtC

theorem Ht.cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem Ht.cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem Ht.cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (hn : n = n') (hi : i = i') (hn' : n' = n'')
    (hi' : i' = i'') (x : Ht q E n i) : (x.cast hn hi).cast hn' hi' = x.cast (hn.trans hn') (hi.trans hi') := by
  subst hn; subst hi; subst hn'; subst hi'; rfl

theorem cup_cast_left {q : ℕ} {E : Spc} {n i n' i' m j : ℤ} (hn : n = n') (hi : i = i') (a : Ht q E n i)
    (b : Ht q E m j) :
    cup q (a.cast hn hi) b = (cup q a b).cast (by rw [hn]) (by rw [hi]) := by
  subst hn; subst hi; rfl

def pairing (q : ℕ) {X : Scheme.{0}} (d : ℕ) (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) {n i : ℤ}
    (a : Ht q (sch.obj X) n i) (b : Ht q (sch.obj X) (2 * d - n) (d - i)) : ZMod q :=
  t ((cup q a b).cast (by ring) (by ring))

def IsPerfect (q : ℕ) {X : Scheme.{0}} (d : ℕ) (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) : Prop :=
  ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = pairing q d t a b

def IsTranspose (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
    (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ)
    (γ : Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))) : Prop :=
  ∀ (a : Ht q (sch.obj Z) b i) (y : Ht q (sch.obj X) (2 * dZ - b) (dZ - i)),
    tX ((cup q (γ a) y).cast (by ring) (by ring)) = tZ ((cup q a (pull _ (sch.map f) _ _ y)).cast (by ring) (by ring))

def pushWith (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
    (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ) :
    Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  pick (IsTranspose q f dZ dX tZ tX b i)

abbrev TrFam : Type 1 := ∀ (q : ℕ) (X : Scheme.{0}) (d : ℕ), Ht q (sch.obj X) (2 * d) d →+ ZMod q

def one0 (q : ℕ) (X : Scheme.{0}) : Ht q (sch.obj X) (2 * ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) :=
  (one q (sch.obj X)).cast (by simp) (by simp)

def IsSection {Y X : Scheme.{0}} (f : Y ⟶ X) (L : cech f ⟶ ofCat (glCat 1)) (s : Γ(Y, ⊤)) : Prop :=
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (a b : U ⟶ Y) (h : ∀ j, ![a, b] j ≫ f = x),
    b.appTop.hom s = (lineUnit L (cechPt f 1 x ![a, b] h) : Γ(U, ⊤)) * a.appTop.hom s

def IsZeroScheme {D Y X : Scheme.{0}} (ι : D ⟶ X) (f : Y ⟶ X) (s : Γ(Y, ⊤)) : Prop :=
  ∀ (U : Scheme.{0}) (g : U ⟶ Y), (∃ h : U ⟶ D, h ≫ ι = g ≫ f) ↔ g.appTop.hom s = 0

def IsTraceFam (T : TrFam) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k],
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (d : ℕ) [SmoothOfRelativeDimension d p], IsPerfect q d (T q X d)) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsIso p],
      T q X 0 (one0 q X) = 1) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X X₁ X₂ : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (d : ℕ) [SmoothOfRelativeDimension d p] (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X), IsIso (coprod.desc j₁ j₂) →
      ∀ y, T q X d y = T q X₁ d (pull _ (sch.map j₁) _ _ y) + T q X₂ d (pull _ (sch.map j₂) _ _ y)) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {X D Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (d : ℕ) [SmoothOfRelativeDimension (d + 1) p] (ι : D ⟶ X) [IsClosedImmersion ι]
      [SmoothOfRelativeDimension d (ι ≫ p)] (f : Y ⟶ X) [Etale f] [Surjective f] (L : cech f ⟶ ofCat (glCat 1))
      (s : Γ(Y, ⊤)), IsSection f L s → IsZeroScheme ι f s → ∀ c : Ht q (sch.obj X) 2 1,
      pull _ (cechAug f) _ _ c = c1 q L → ∀ y : Ht q (sch.obj X) (2 * d) d,
      T q X (d + 1) ((cup q c y).cast (by push_cast; ring) (by push_cast; ring)) = T q D d (pull _ (sch.map ι) _ _ y)) ∧
    (∀ (Q q : ℕ) [NeZero Q] [NeZero q] (hqQ : q ∣ Q), IsUnit (Q : k) → ∀ {X : Scheme.{0}}
      (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
      (y : Ht Q (sch.obj X) (2 * d) d), T q X d (red Q q (sch.obj X) _ _ y) = ZMod.castHom hqQ (ZMod q) (T Q X d y))

def tr : TrFam := pick IsTraceFam

def gysin (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (b i : ℤ) :
    Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  pushWith q f dZ dX (tr q Z dZ) (tr q X dX) b i

section API

variable {q : ℕ}

theorem Ht.cast_self {E : Spc} {n i : ℤ} (hn : n = n) (hi : i = i) (x : Ht q E n i) : x.cast hn hi = x := rfl

theorem cup_cast_right {E : Spc} {n i m j m' j' : ℤ} (hm : m = m') (hj : j = j') (a : Ht q E n i)
    (b : Ht q E m j) :
    cup q a (b.cast hm hj) = (cup q a b).cast (by rw [hm]) (by rw [hj]) := by
  subst hm; subst hj; rfl

def Ht.castHom {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : Ht q E n i →+ Ht q E n' i' where
  toFun x := x.cast hn hi
  map_zero' := Ht.cast_zero hn hi
  map_add' := Ht.cast_add hn hi

theorem Ht.castHom_apply {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    Ht.castHom hn hi x = x.cast hn hi := rfl

variable {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
  (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ)

private theorem hm : 2 * (dX : ℤ) - (b + 2 * ((dX : ℤ) - dZ)) = 2 * dZ - b := by ring
private theorem hj : (dX : ℤ) - (i + ((dX : ℤ) - dZ)) = dZ - i := by ring

def form (a : Ht q (sch.obj Z) b i) :
    Ht q (sch.obj X) (2 * dX - (b + 2 * ((dX : ℤ) - dZ))) (dX - (i + ((dX : ℤ) - dZ))) →+ ZMod q :=
  ((tZ.comp (Ht.castHom (by ring) (by ring))).comp (cup q a)).comp
    ((pull _ (sch.map f) _ _).comp (Ht.castHom (hm dZ dX b) (hj dZ dX i)))

theorem form_add (a a' : Ht q (sch.obj Z) b i) : form f dZ dX tZ b i (a + a') = form f dZ dX tZ b i a + form f dZ dX tZ b i a' := by
  ext y
  simp only [form, AddMonoidHom.comp_apply, map_add, AddMonoidHom.add_apply]

variable {f dZ dX tZ tX b i}

theorem pairing_add {d : ℕ} (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) {n j : ℤ} (c c' : Ht q (sch.obj X) n j)
    (y : Ht q (sch.obj X) (2 * d - n) (d - j)) : pairing q d t (c + c') y = pairing q d t c y + pairing q d t c' y := by
  simp only [pairing, map_add, AddMonoidHom.add_apply, Ht.cast_add]

theorem pairing_zero {d : ℕ} (t : Ht q (sch.obj X) (2 * d) d →+ ZMod q) {n j : ℤ}
    (y : Ht q (sch.obj X) (2 * d - n) (d - j)) : pairing q d t (0 : Ht q (sch.obj X) n j) y = 0 := by
  simp only [pairing, map_zero, AddMonoidHom.zero_apply, Ht.cast_zero]

theorem pairing_iff (a : Ht q (sch.obj Z) b i) (c : Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))) :
    (∀ y, form f dZ dX tZ b i a y = pairing q dX tX c y) ↔
      ∀ y : Ht q (sch.obj X) (2 * dZ - b) (dZ - i),
        tX ((cup q c y).cast (by ring) (by ring)) = tZ ((cup q a (pull _ (sch.map f) _ _ y)).cast (by ring) (by ring)) := by
  constructor
  · intro h y
    have := h (y.cast (hm dZ dX b).symm (hj dZ dX i).symm)
    simp only [form, pairing, AddMonoidHom.comp_apply, Ht.castHom_apply, Ht.cast_cast, Ht.cast_self,
      cup_cast_right] at this
    exact this.symm
  · intro h y
    have := h (y.cast (hm dZ dX b) (hj dZ dX i))
    simp only [form, pairing, AddMonoidHom.comp_apply, Ht.castHom_apply, cup_cast_right, Ht.cast_cast] at this ⊢
    exact this.symm

theorem exists_isTranspose (hX : IsPerfect q dX tX) : ∃ γ, IsTranspose q f dZ dX tZ tX b i γ := by
  choose c hc hu using fun a => hX _ _ (form f dZ dX tZ b i a)
  refine ⟨AddMonoidHom.mk' c fun a a' => ?_, fun a y => ((pairing_iff a (c a)).1 (hc a)) y⟩
  refine (hu (a + a') _ fun y => ?_).symm
  rw [form_add, AddMonoidHom.add_apply, hc a y, hc a' y, pairing_add]

theorem IsTranspose.unique (hX : IsPerfect q dX tX) {γ γ' : Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))}
    (h : IsTranspose q f dZ dX tZ tX b i γ) (h' : IsTranspose q f dZ dX tZ tX b i γ') : γ = γ' := by
  ext a
  obtain ⟨c, _, hu⟩ := hX _ _ (form f dZ dX tZ b i a)
  exact (hu _ ((pairing_iff a (γ a)).2 (h a))).trans (hu _ ((pairing_iff a (γ' a)).2 (h' a))).symm

theorem pushWith_isTranspose (hX : IsPerfect q dX tX) : IsTranspose q f dZ dX tZ tX b i (pushWith q f dZ dX tZ tX b i) :=
  pick_spec (exists_isTranspose hX)

theorem pushWith_eq_iff (hX : IsPerfect q dX tX) (γ : Ht q (sch.obj Z) b i →+ Ht q (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ))) :
    pushWith q f dZ dX tZ tX b i = γ ↔ IsTranspose q f dZ dX tZ tX b i γ :=
  ⟨fun e => e ▸ pushWith_isTranspose hX, fun h => (pushWith_isTranspose hX).unique hX h⟩

theorem pushWith_id {d : ℕ} {t : Ht q (sch.obj X) (2 * d) d →+ ZMod q} (ht : IsPerfect q d t) :
    pushWith q (𝟙 X) d d t t b i = Ht.castHom (by ring) (by ring) := by
  rw [pushWith_eq_iff ht]
  intro a y
  rw [CategoryTheory.Functor.map_id, pull_id, Ht.castHom_apply, cup_cast_left, Ht.cast_cast]

end API

theorem tr_spec (h : ∃ T, IsTraceFam T) : IsTraceFam tr := pick_spec h

theorem gysin_isTranspose (h : ∃ T, IsTraceFam T) (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) [NeZero q]
    (hq : IsUnit (q : k)) {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (dZ dX : ℕ)
    [SmoothOfRelativeDimension dX p] (b i : ℤ) :
    IsTranspose q f dZ dX (tr q Z dZ) (tr q X dX) b i (gysin q f dZ dX b i) :=
  pushWith_isTranspose ((tr_spec h k).1 q hq p dX)

theorem gysin_id (h : ∃ T, IsTraceFam T) (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) [NeZero q]
    (hq : IsUnit (q : k)) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ)
    [SmoothOfRelativeDimension d p] (b i : ℤ) :
    gysin q (𝟙 X) d d b i = Ht.castHom (by ring) (by ring) :=
  pushWith_id ((tr_spec h k).1 q hq p d)

example : ¬ IsTraceFam 0 := by
  intro h
  have h2 : IsUnit ((2 : ℕ) : AlgebraicClosure ℚ) := isUnit_iff_ne_zero.2 (by norm_num)
  have := (h (AlgebraicClosure ℚ)).2.1 2 h2 (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
  simp at this

section Adic
variable (l : ℕ) [Fact l.Prime]

def gysinHl {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (b i : ℤ) :
    Hl l (sch.obj Z) b i →ₗ[ℤ_[l]] Hl l (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  pick fun g => ∀ (x : Hl l (sch.obj Z) b i) (k : ℕ), (g x).1 k = gysin (l ^ k) f dZ dX b i (x.1 k)

def gysinHQ {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (b i : ℤ) :
    HQ l (sch.obj Z) b i →ₗ[ℚ_[l]] HQ l (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)) :=
  (gysinHl l f dZ dX b i).baseChange ℚ_[l]

theorem gysinHl_apply {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (b i : ℤ)
    (h : ∃ g : Hl l (sch.obj Z) b i →ₗ[ℤ_[l]] Hl l (sch.obj X) (b + 2 * ((dX : ℤ) - dZ)) (i + ((dX : ℤ) - dZ)),
      ∀ (x : Hl l (sch.obj Z) b i) (k : ℕ), (g x).1 k = gysin (l ^ k) f dZ dX b i (x.1 k))
    (x : Hl l (sch.obj Z) b i) (k : ℕ) : (gysinHl l f dZ dX b i x).1 k = gysin (l ^ k) f dZ dX b i (x.1 k) :=
  pick_spec h x k

example {ι : Type} [LinearOrder ι] {X : Scheme.{0}} (I : ι → X.IdealSheafData) (s : ℕ) (j : Fin (s + 2)) (d : ℕ)
    (hs : s + 1 ≤ d) (b i : ℤ) :
    Ht (l ^ 2) (sch.obj (GlobalTheory.Strata.Ystr I (s + 1))) b i →+ Ht (l ^ 2) (sch.obj (GlobalTheory.Strata.Ystr I s)) (b + 2) (i + 1) :=
  (Ht.castHom (by push_cast [Nat.cast_sub hs, Nat.cast_sub (Nat.le_of_succ_le hs)]; ring)
      (by push_cast [Nat.cast_sub hs, Nat.cast_sub (Nat.le_of_succ_le hs)]; ring)).comp
    (gysin (l ^ 2) (GlobalTheory.Strata.δ I s j) (d - (s + 1)) (d - s) b i)

end Adic

end GlobalTheory.EtC.Gysin

end
