import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.LCycleCut

def Dbl {X : Scheme.{0}} (U : X.Opens) : Spc := pushout (sch.map U.ι) (sch.map U.ι)

def i1 {X : Scheme.{0}} (U : X.Opens) : sch.obj X ⟶ Dbl U := pushout.inl _ _

def i2 {X : Scheme.{0}} (U : X.Opens) : sch.obj X ⟶ Dbl U := pushout.inr _ _

def fold {X : Scheme.{0}} (U : X.Opens) : Dbl U ⟶ sch.obj X := pushout.desc (𝟙 _) (𝟙 _) rfl

def dmap {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) : Dbl U' ⟶ Dbl U :=
  pushout.map _ _ _ _ (sch.map f) (sch.map f) (sch.map (f.resLE U U' h))
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])

def off {Z X : Scheme.{0}} (ι : Z ⟶ X) : X.Opens := ⟨interior (Set.range ι)ᶜ, isOpen_interior⟩

structure SmPair {k : Type} [Field k] (d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X) : Prop where
  closed : IsClosedImmersion ι
  qc : QuasiCompact p
  sep : IsSeparated p
  big : SmoothOfRelativeDimension (e + d) p
  small : SmoothOfRelativeDimension e (ι ≫ p)

abbrev TFam (l : ℕ) (k : Type) [Field k] (w : ℕ → ℤ) : Type 1 :=
  ∀ (j d : ℕ) {X : Scheme.{0}} (_ : X ⟶ S k) (U : X.Opens), Ht (l ^ j) (Dbl U) (2 * d) (w d)

structure IsThom {l : ℕ} {k : Type} [Field k] {w : ℕ → ℤ} (τ : TFam l k w) : Prop where
  supp : ∀ (j d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι →
    pull _ (i2 (off ι)) _ _ (τ j d p (off ι)) = 0
  nat : ∀ (j d e' e : ℕ) {Z' X' Z X : Scheme.{0}} (p' : X' ⟶ S k) (ι' : Z' ⟶ X') (p : X ⟶ S k) (ι : Z ⟶ X),
    SmPair d e' p' ι' → SmPair d e p ι → ∀ (f : X' ⟶ X) (g : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' g f ι →
    ∀ h : off ι' ≤ f ⁻¹ᵁ off ι, pull _ (dmap f _ _ h) _ _ (τ j d p (off ι)) = τ j d p' (off ι')
  gen : ∀ (j d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (y : Pt p), SmPair d 0 p y.1 →
    ∀ a : Ht (l ^ j) (Dbl (off y.1)) (2 * d) (w d), pull _ (i2 (off y.1)) _ _ a = 0 → ∃ r : ℕ, a = r • τ j d p (off y.1)
  red : ∀ (j d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι →
    red (l ^ (j + 1)) (l ^ j) _ _ _ (τ (j + 1) d p (off ι)) = τ j d p (off ι)

def lev {l : ℕ} {k : Type} [Field k] (τ : TFam l k fun _ => 0) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (U : X.Opens) (j : ℕ) :
    Ht (l ^ j) (sch.obj X) (2 * d) 0 := pull _ (i1 U) _ _ (τ j d p U)

open Classical in

def cyc {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (τ : TFam l k fun _ => 0) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k)
    (U : X.Opens) : V l X (2 * d) :=
  if h : (lev τ d p U : ∀ j, HtL l j (sch.obj X) (2 * d) 0) ∈ HlSub l (sch.obj X) (2 * d) 0 then (1 : ℚ_[l]) ⊗ₜ ⟨_, h⟩ else 0

def LDbl : Prop := Base → ∀ (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} (U : X.Opens),
  (∀ (n : ℤ) (x : H R (sch.obj X) F n), pull R (sch.map U.ι) F n x = 0 →
    ∃ a : H R (Dbl U) F n, pull R (i1 U) F n a = x ∧ pull R (i2 U) F n a = 0) ∧
  ∀ m : ℤ, Function.Surjective (pull R (sch.map U.ι) F m) →
    ∀ a : H R (Dbl U) F (m + 1), pull R (i1 U) F _ a = 0 → pull R (i2 U) F _ a = 0 → a = 0

def LExc : Prop := Base → ∀ (R : Type) [CommRing R] (F : Shv R) {Z X' X : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X),
  Etale f → IsClosedImmersion ι → IsPullback ι' (𝟙 Z) f ι → ∀ (h : off ι' ≤ f ⁻¹ᵁ off ι) (n : ℤ),
  (∀ a : H R (Dbl (off ι)) F n, pull R (i2 _) F n a = 0 → pull R (dmap f _ _ h) F n a = 0 → a = 0) ∧
  ∀ a' : H R (Dbl (off ι')) F n, pull R (i2 _) F n a' = 0 →
    ∃ a : H R (Dbl (off ι)) F n, pull R (i2 _) F n a = 0 ∧ pull R (dmap f _ _ h) F n a = a'

def LDisj : Prop := Base → ∀ (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} (U : X.Opens) (I : Type) [Finite I]
  (W : I → X.Opens), U ⊔ iSup W = ⊤ → (∀ i j, i ≠ j → W i ⊓ W j ≤ U) → ∀ (n : ℤ) (a : H R (Dbl U) F n),
  pull R (i2 U) F n a = 0 → (∀ i, pull R (dmap (W i).ι ((W i).ι ⁻¹ᵁ U) U le_rfl) F n a = 0) → a = 0

def LSemi : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (d e : ℕ) {Z X : Scheme.{0}}
  (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι → ∀ n i : ℤ, n < 2 * d →
  ∀ a : Ht q (Dbl (off ι)) n i, pull _ (i2 _) _ _ a = 0 → a = 0

def LSupp : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {Z X : Scheme.{0}}
  (p : X ⟶ S k) (ι : Z ⟶ X), IsClosedImmersion ι → QuasiCompact p → IsSeparated p → LocallyOfFiniteType p →
  ∀ (n m i j : ℤ) (a : Ht q (Dbl (off ι)) n i) (b : Ht q (sch.obj X) m j), pull _ (i2 _) _ _ a = 0 →
  pull _ (sch.map ι) _ _ b = 0 → cup q (E := sch.obj X) (pull _ (i1 _) _ _ a) b = 0

def LThom : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∃ τ : TFam l k fun d => d, IsThom τ

def LUnit : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ i : ℤ,
  ∃ (u : Ht q (sch.obj (S k)) 0 i) (v : Ht q (sch.obj (S k)) 0 (-i)),
    (cup q u v).cast (add_zero 0) (add_neg_cancel i) = one q (sch.obj (S k))

def LUntwist : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ τ : TFam l k fun d => d, IsThom τ → ∃ τ' : TFam l k fun _ => 0, IsThom τ'

def LNat : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (τ : TFam l k fun _ => 0), IsThom τ →
  ∀ (d e' e : ℕ) {Z' X' Z X : Scheme.{0}} (p' : X' ⟶ S k) (ι' : Z' ⟶ X') (p : X ⟶ S k) (ι : Z ⟶ X),
  SmPair d e' p' ι' → SmPair d e p ι → ∀ (f : X' ⟶ X) (g : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' g f ι →
  pb l f _ (cyc τ d p (off ι)) = cyc τ d p' (off ι')

def LKill : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ τ : TFam l k fun _ => 0, IsThom τ →
  ∀ (d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d e p ι → ∀ (m : ℤ) (β : V l X m),
  pb l ι m β = 0 → cupV l X rfl (cyc τ d p (off ι)) β = 0

def LPts : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {Z : Scheme.{0}} (r : Z ⟶ S k), Etale r →
  (∀ t : Pt r, IsOpenImmersion t.1) ∧ ∀ z : Z, ∃ t : Pt r, z ∈ Set.range t.1

def LAdd : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (τ : TFam l k fun _ => 0), IsThom τ →
  ∀ (d : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X), SmPair d 0 p ι → ∀ s : Finset (Pt p),
  (∀ y, y ∈ s ↔ ∃ t : S k ⟶ Z, t ≫ ι = y.1) → cyc τ d p (off ι) = ∑ y ∈ s, cyc τ d p (off y.1)

def LSpan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (τ : TFam l k fun _ => 0), IsThom τ →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (y : Pt p), SmPair d 0 p y.1 →
  ∀ z : V l X (2 * d), pb l (off y.1).ι _ z = 0 → ∃ r : ℚ_[l], z = r • cyc τ d p (off y.1)

def LGeom : Prop := ∀ (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p →
  SmPair d d (pullback.fst p p ≫ p) (pullback.diagonal p) ∧
  (∀ y : Pt p, SmPair d 0 p y.1 ∧ ∀ h, IsPullback y.1 y.1 (pullback.lift (𝟙 X) (p ≫ y.1) h) (pullback.diagonal p)) ∧
  ∀ {Y : Scheme.{0}} (q : Y ⟶ S k), SP d q → ∀ (c a : Y ⟶ X), c ≫ p = q → Etale (equalizer.ι c a ≫ q) → ∀ h,
    SmPair d 0 q (equalizer.ι c a) ∧
    IsPullback (equalizer.ι c a) (equalizer.ι c a ≫ c) (pullback.lift c a h) (pullback.diagonal p)

theorem pb_comp (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l g n (pb l f n x) = pb l (g ≫ f) n x := by
  simp only [pb, pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp, LinearMap.comp_apply]

theorem goal_of (_h1 : LDbl) (_h2 : LExc) (_h3 : LDisj) (_h4 : LSemi) (_h5 : LSupp) (hT : LThom) (_h7 : LUnit) (hU : LUntwist)
    (hN : LNat) (hK : LKill) (_h11 : LPts) (hA : LAdd) (hS : LSpan) (hG : LGeom) : LCycle := by
  intro B l _ k _ _ hl
  obtain ⟨τ₀, h₀⟩ := hT B l k hl
  obtain ⟨τ, hτ⟩ := hU B l k hl τ₀ h₀
  let δ : Fam l k := fun d _ p => cyc τ d (pullback.fst p p ≫ p) (off (pullback.diagonal p))
  have hcl : ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ y : Pt p, δ.cl d y = cyc τ d p (off y.1) := by
    intro d X p hp y
    obtain ⟨hd, hy, -⟩ := hG k d p hp
    exact hN l k τ hτ d 0 d p y.1 _ _ (hy y).1 hd _ y.1 (by rw [pullback.lift_fst_assoc, Category.id_comp]) ((hy y).2 _)
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro d X p hp m β
    have h := hK B l k hl τ hτ d d _ _ (hG k d p hp).1 m (pb l (pullback.fst p p) m β - pb l (pullback.snd p p) m β)
      (by rw [map_sub, pb_comp, pb_comp, pullback.diagonal_fst, pullback.diagonal_snd, sub_self])
    rw [map_sub, sub_eq_zero] at h
    exact h
  · intro d Y X q p hq hp c a hc ha he s hs
    obtain ⟨hd, -, hE⟩ := hG k d p hp
    obtain ⟨hE1, hE2⟩ := hE q hq c a hc he (hc.trans ha.symm)
    have h1 : δ.corr d c a hc ha = cyc τ d q (off (equalizer.ι c a)) :=
      hN l k τ hτ d 0 d q _ _ _ hE1 hd _ _ (by rw [pullback.lift_fst_assoc, hc]) hE2
    rw [h1, hA B l k τ hτ d q _ hE1 s fun y => (hs y).trans
      ⟨fun h => ⟨equalizer.lift y.1 h, equalizer.lift_ι _ _⟩, fun ⟨t, ht⟩ => by
        rw [← ht, Category.assoc, Category.assoc, equalizer.condition]⟩]
    exact Finset.sum_congr rfl fun y _ => (hcl d q hq y).symm
  · intro d X p hp y U hU' z hz
    have hy := ((hG k d p hp).2.1 y).1
    have : U = off y.1 := by
      ext1
      change (U : Set X) = interior _
      rw [← hU', U.isOpen.interior_eq]
    subst this
    rw [hcl d p hp y]
    exact hS B l k τ hτ d p y hy z hz

end LateralTheory.EtaleTrace.LCycleCut

end
