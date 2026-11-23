import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.ConeKillC

universe w

variable {R : Type} [CommRing R]

section Basic

variable {K L : Cx.{w} R}

theorem cls_surj (K : Cx.{w} R) (n : ℕ) (c : K.H n) : ∃ x hx, K.cls x hx = c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z.1, z.2, rfl⟩

theorem cls_eq_zero (K : Cx.{w} R) {n : ℕ} (x : K.X n) (hx : K.d n x = 0) : K.cls x hx = 0 ↔ x ∈ K.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem cls_congr (K : Cx.{w} R) {n : ℕ} {x y : K.X n} (e : x = y) (hx : K.d n x = 0) (hy : K.d n y = 0) :
    K.cls x hx = K.cls y hy := by
  subst e
  rfl

theorem cls_add (K : Cx.{w} R) {n : ℕ} (x y : K.X n) (hx : K.d n x = 0) (hy : K.d n y = 0) (hz : K.d n (x + y) = 0) :
    K.cls (x + y) hz = K.cls x hx + K.cls y hy := rfl

theorem cls_sub (K : Cx.{w} R) {n : ℕ} (x y : K.X n) (hx : K.d n x = 0) (hy : K.d n y = 0) (hz : K.d n (x - y) = 0) :
    K.cls (x - y) hz = K.cls x hx - K.cls y hy := rfl

theorem mapH_cls (φ : Cx.Hom K L (RingHom.id R)) (n : ℕ) (x : K.X n) (hx : K.d n x = 0) (h : L.d n (φ.f n x) = 0) :
    φ.mapH n (K.cls x hx) = L.cls (φ.f n x) h := rfl

theorem mem_B_of_sub {n : ℕ} (h : Subsingleton (K.H n)) (x : K.X n) (hx : K.d n x = 0) : x ∈ K.B n :=
  (cls_eq_zero K x hx).1 (Subsingleton.elim _ _)

theorem sub_of_mem_B {n : ℕ} (h : ∀ x, K.d n x = 0 → x ∈ K.B n) : Subsingleton (K.H n) := by
  refine ⟨fun c c' => ?_⟩
  obtain ⟨x, hx, rfl⟩ := cls_surj K n c
  obtain ⟨y, hy, rfl⟩ := cls_surj K n c'
  rw [(cls_eq_zero K x hx).2 (h x hx), (cls_eq_zero K y hy).2 (h y hy)]

structure AD (K L : Cx.{w} R) where
  r : ∀ n, K.X n →ₗ[R] L.X (n + 1)
  anti : ∀ n x, L.d (n + 1) (r n x) + r (n + 1) (K.d n x) = 0

structure NH (t : AD K L) where
  h : ∀ n, K.X n →ₗ[R] L.X n
  eq : ∀ n x, L.d n (h n x) - h (n + 1) (K.d n x) = t.r n x

def AD.ofH (h : ∀ n, K.X n →ₗ[R] L.X n) : AD K L where
  r n := (L.d n).comp (h n) - (h (n + 1)).comp (K.d n)
  anti n x := by
    change L.d (n + 1) (L.d n (h n x) - h (n + 1) (K.d n x)) +
      (L.d (n + 1) (h (n + 1) (K.d n x)) - h (n + 2) (K.d (n + 1) (K.d n x))) = 0
    rw [map_sub, L.dd, K.dd, map_zero]
    abel

def NH.ofH (h : ∀ n, K.X n →ₗ[R] L.X n) : NH (AD.ofH h) := ⟨h, fun n x => rfl⟩

def altCx (R : Type) [CommRing R] : Cx.{0} R where
  X _ := R
  d n := if Even n then LinearMap.id else 0
  dd n x := by
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      simp [h, h']
    · simp [h]

def exH (R : Type) [CommRing R] : ∀ n, (altCx R).X n →ₗ[R] (altCx R).X n :=
  fun n => if n = 0 then LinearMap.id else 0

theorem exH_zero (R : Type) [CommRing R] (y : R) : (show R from exH R 0 y) = y := by
  change (if (0 : ℕ) = 0 then LinearMap.id else 0 : R →ₗ[R] R) y = y
  simp

theorem exH_one (R : Type) [CommRing R] (y : R) : (show R from exH R 1 y) = 0 := by
  change (if (1 : ℕ) = 0 then LinearMap.id else 0 : R →ₗ[R] R) y = 0
  simp

theorem alt_zero (R : Type) [CommRing R] (y : R) : (show R from (altCx R).d 0 y) = y := by
  change (if Even 0 then LinearMap.id else 0 : R →ₗ[R] R) y = y
  simp

theorem exAD_ne (R : Type) [CommRing R] [Nontrivial R] : ∃ x : (altCx R).X 0, (AD.ofH (exH R)).r 0 x ≠ 0 := by
  refine ⟨(1 : R), fun h0 => one_ne_zero (α := R) ?_⟩
  have e : (show R from (altCx R).d 0 (show R from exH R 0 (1 : R))) - (show R from exH R 1 (show R from (altCx R).d 0 (1 : R))) = 0 := h0
  rwa [exH_zero, alt_zero, exH_one, sub_zero] at e

theorem exNH_ne (R : Type) [CommRing R] [Nontrivial R] : ∃ x : (altCx R).X 0, (NH.ofH (exH R)).h 0 x ≠ 0 :=
  ⟨(1 : R), fun h0 => one_ne_zero (α := R) ((exH_zero R 1).symm.trans h0)⟩

def cone (t : AD K L) : Cx.{w} R where
  X n := L.X n × K.X n
  d n := ((L.d n).comp (LinearMap.fst R _ _) + (t.r n).comp (LinearMap.snd R _ _)).prod ((K.d n).comp (LinearMap.snd R _ _))
  dd n x := by
    refine Prod.ext ?_ (K.dd n x.2)
    change L.d (n + 1) (L.d n x.1 + t.r n x.2) + t.r (n + 1) (K.d n x.2) = 0
    rw [map_add, L.dd, zero_add, t.anti]

theorem cone_d (t : AD K L) (n : ℕ) (b : L.X n) (x : K.X n) :
    (cone t).d n ((b, x) : L.X n × K.X n) = ((L.d n b + t.r n x, K.d n x) : L.X (n + 1) × K.X (n + 1)) := rfl

def inc (t : AD K L) : Cx.Hom L (cone t) (RingHom.id R) where
  f n := LinearMap.inl R _ _
  comm n x := by
    refine Prod.ext ?_ ?_
    · change L.d n x + t.r n 0 = L.d n x
      rw [map_zero, add_zero]
    · change K.d n 0 = 0
      rw [map_zero]

def pr (t : AD K L) : Cx.Hom (cone t) K (RingHom.id R) where
  f n := LinearMap.snd R _ _
  comm n x := rfl

def sec {t : AD K L} (u : NH t) : Cx.Hom K (cone t) (RingHom.id R) where
  f n := (-(u.h n)).prod LinearMap.id
  comm n x := by
    refine Prod.ext ?_ rfl
    change L.d n (-(u.h n x)) + t.r n x = -(u.h (n + 1) (K.d n x))
    rw [← u.eq n x, map_neg]
    abel

theorem cone_one (t : AD K L) (u : NH t) (j : ℕ) (hL : Subsingleton (L.H j)) (hK : Subsingleton (K.H j)) :
    Subsingleton ((cone t).H j) := by
  refine sub_of_mem_B fun z hz => ?_
  obtain ⟨b, x⟩ := z
  have h1 : L.d j b + t.r j x = 0 := congrArg Prod.fst hz
  have h2 : K.d j x = 0 := congrArg Prod.snd hz
  have h3 : L.d j (b + u.h j x) = 0 := by
    have := u.eq j x
    rw [h2, map_zero, sub_zero] at this
    rw [map_add, this, h1]
  have m1 := mem_B_of_sub hL _ h3
  have m2 := mem_B_of_sub hK _ h2
  cases j with
  | zero =>
    have e2 : x = 0 := m2
    subst e2
    have e1 : b + u.h 0 0 = 0 := m1
    rw [map_zero, add_zero] at e1
    subst e1
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨c, hc⟩ := m1
    obtain ⟨y, rfl⟩ := m2
    refine ⟨(c - u.h j y, y), ?_⟩
    refine Prod.ext ?_ rfl
    change L.d j (c - u.h j y) + t.r j y = b
    rw [← u.eq j y, map_sub, hc]
    abel

theorem kill (t : AD K L) (j : ℕ) (hs : Function.Surjective ((pr t).mapH j)) (x : K.X j) (hx : K.d j x = 0) :
    t.r j x ∈ L.B (j + 1) := by
  obtain ⟨c, hc⟩ := hs (K.cls x hx)
  obtain ⟨⟨b, y⟩, hz, rfl⟩ := cls_surj _ _ c
  have h1 : L.d j b + t.r j y = 0 := congrArg Prod.fst hz
  have h2 : K.d j y = 0 := congrArg Prod.snd hz
  have h3 : K.cls y h2 - K.cls x hx = 0 := sub_eq_zero.2 hc
  have h4 : y - x ∈ K.B j := (cls_eq_zero K (y - x) (by rw [map_sub, h2, hx, sub_zero])).1 h3
  cases j with
  | zero =>
    have e : y - x = 0 := h4
    rw [sub_eq_zero] at e
    subst e
    exact ⟨-b, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_right h1).symm⟩
  | succ j =>
    obtain ⟨v, hv⟩ := h4
    refine ⟨t.r j v - b, ?_⟩
    have e : x = y - K.d j v := by rw [hv]; abel
    have := t.anti j v
    rw [e, map_sub, map_sub]
    rw [eq_neg_of_add_eq_zero_left h1]
    rw [eq_neg_of_add_eq_zero_left this]
    abel

def secM (t : AD K L) (u : NH t) (c : ℕ) (l : K.H c →ₗ[R] L.H c) : K.H c →ₗ[R] (cone t).H c :=
  (sec u).mapH c + ((inc t).mapH c).comp l

theorem pr_inc (t : AD K L) (c : ℕ) (z : L.H c) : (pr t).mapH c ((inc t).mapH c z) = 0 := by
  obtain ⟨b, hb, rfl⟩ := cls_surj L c z
  exact (cls_eq_zero K _ _).2 (Submodule.zero_mem _)

theorem pr_secM (t : AD K L) (u : NH t) (c : ℕ) (l : K.H c →ₗ[R] L.H c) (y : K.H c) :
    (pr t).mapH c (secM t u c l y) = y := by
  obtain ⟨x, hx, rfl⟩ := cls_surj K c y
  change (pr t).mapH c ((sec u).mapH c (K.cls x hx) + (inc t).mapH c (l (K.cls x hx))) = _
  rw [map_add, pr_inc, add_zero]
  rfl

theorem secM_eq (t : AD K L) (u u' : NH t) (c : ℕ) (l l' : K.H c →ₗ[R] L.H c)
    (h : ∀ x hx hz, L.cls (u.h c x - u'.h c x) hz = l (K.cls x hx) - l' (K.cls x hx)) : secM t u c l = secM t u' c l' := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, hx, rfl⟩ := cls_surj K c y
  have hz : L.d c (u.h c x - u'.h c x) = 0 := by
    have e := u.eq c x
    have e' := u'.eq c x
    rw [hx, map_zero, sub_zero] at e e'
    rw [map_sub, e, e', sub_self]
  change (sec u).mapH c (K.cls x hx) + (inc t).mapH c (l (K.cls x hx)) =
    (sec u').mapH c (K.cls x hx) + (inc t).mapH c (l' (K.cls x hx))
  have e2 : (inc t).mapH c (l (K.cls x hx)) - (inc t).mapH c (l' (K.cls x hx)) =
      (inc t).mapH c (L.cls _ hz) := by rw [← map_sub, h x hx hz]
  have e1 : (sec u).mapH c (K.cls x hx) - (sec u').mapH c (K.cls x hx) + (inc t).mapH c (L.cls _ hz) = 0 := by
    have hw : ((sec u).f c x - (sec u').f c x + (inc t).f c (u.h c x - u'.h c x)) = 0 := by
      refine Prod.ext ?_ ?_
      · change -(u.h c x) - -(u'.h c x) + (u.h c x - u'.h c x) = 0
        abel
      · change x - x + 0 = 0
        abel
    have hc : ∀ v (hv : (cone t).d c v = 0), v = 0 → (cone t).cls v hv = 0 := by
      intro v hv e
      subst e
      exact ((cls_eq_zero _ _ _).2 (Submodule.zero_mem _))
    have hv : (cone t).d c ((sec u).f c x - (sec u').f c x + (inc t).f c (u.h c x - u'.h c x)) = 0 := by rw [hw, map_zero]
    exact hc _ hv hw
  rw [← sub_eq_zero]
  have e3 : (sec u).mapH c (K.cls x hx) + (inc t).mapH c (l (K.cls x hx)) -
      ((sec u').mapH c (K.cls x hx) + (inc t).mapH c (l' (K.cls x hx))) =
      ((sec u).mapH c (K.cls x hx) - (sec u').mapH c (K.cls x hx) + (inc t).mapH c (L.cls _ hz)) +
      ((inc t).mapH c (l (K.cls x hx)) - (inc t).mapH c (l' (K.cls x hx)) - (inc t).mapH c (L.cls _ hz)) := by abel
  rw [e3, e1, e2, sub_self, add_zero]

variable {K' L' : Cx.{w} R}

def coneHom (t : AD K L) (t' : AD K' L') (f : Cx.Hom K K' (RingHom.id R)) (g : Cx.Hom L L' (RingHom.id R))
    (hc : ∀ n x, t'.r n (f.f n x) = g.f (n + 1) (t.r n x)) : Cx.Hom (cone t) (cone t') (RingHom.id R) where
  f n := (g.f n).prodMap (f.f n)
  comm n x := by
    refine Prod.ext ?_ (f.comm n x.2)
    change L'.d n (g.f n x.1) + t'.r n (f.f n x.2) = g.f (n + 1) (L.d n x.1 + t.r n x.2)
    rw [hc, g.comm, map_add]

theorem secM_nat (t : AD K L) (t' : AD K' L') (f : Cx.Hom K K' (RingHom.id R)) (g : Cx.Hom L L' (RingHom.id R))
    (hc : ∀ n x, t'.r n (f.f n x) = g.f (n + 1) (t.r n x)) (u : NH t) (u' : NH t') (c : ℕ) (l : K.H c →ₗ[R] L.H c)
    (l' : K'.H c →ₗ[R] L'.H c) (hu : ∀ x, u'.h c (f.f c x) = g.f c (u.h c x))
    (hl : ∀ y, l' (f.mapH c y) = g.mapH c (l y)) (y : K.H c) :
    secM t' u' c l' (f.mapH c y) = (coneHom t t' f g hc).mapH c (secM t u c l y) := by
  have hi : ∀ z : L.H c, (inc t').mapH c (g.mapH c z) = (coneHom t t' f g hc).mapH c ((inc t).mapH c z) := by
    intro z
    obtain ⟨b, hb, rfl⟩ := cls_surj L c z
    have e : (inc t').f c (g.f c b) = (coneHom t t' f g hc).f c ((inc t).f c b) :=
      Prod.ext rfl (by change 0 = f.f c 0; rw [map_zero])
    exact cls_congr _ e _ _
  obtain ⟨x, hx, rfl⟩ := cls_surj K c y
  change (sec u').mapH c (f.mapH c (K.cls x hx)) + (inc t').mapH c (l' (f.mapH c (K.cls x hx))) =
    (coneHom t t' f g hc).mapH c ((sec u).mapH c (K.cls x hx) + (inc t).mapH c (l (K.cls x hx)))
  rw [map_add, hl, hi]
  congr 1
  have e : (sec u').f c (f.f c x) = (coneHom t t' f g hc).f c ((sec u).f c x) :=
    Prod.ext (by change -(u'.h c (f.f c x)) = g.f c (-(u.h c x)); rw [hu, map_neg]) rfl
  exact cls_congr _ e _ _

end Basic

section Shift

def shX (A : Cx.{w} R) : ℕ → Type w
  | 0 => PUnit.{w + 1}
  | n + 1 => A.X n

instance shAb (A : Cx.{w} R) : ∀ n, AddCommGroup (shX A n)
  | 0 => (inferInstance : AddCommGroup PUnit.{w + 1})
  | n + 1 => (inferInstance : AddCommGroup (A.X n))

instance shMd (A : Cx.{w} R) : ∀ n, Module R (shX A n)
  | 0 => (inferInstance : Module R PUnit.{w + 1})
  | n + 1 => (inferInstance : Module R (A.X n))

def shD (A : Cx.{w} R) : ∀ n, shX A n →ₗ[R] shX A (n + 1)
  | 0 => 0
  | n + 1 => (-(A.d n) : A.X n →ₗ[R] A.X (n + 1))

def sh (A : Cx.{w} R) : Cx.{w} R where
  X := shX A
  d := shD A
  dd n x := by
    cases n with
    | zero => exact map_zero (shD A 1)
    | succ n =>
      change -(A.d (n + 1)) (-(A.d n x)) = 0
      rw [map_neg, A.dd, neg_zero, neg_zero]

variable {A A' : Cx.{w} R}

def shFf (φ : Cx.Hom A A' (RingHom.id R)) : ∀ n, shX A n →ₗ[R] shX A' n
  | 0 => 0
  | n + 1 => φ.f n

def shF (φ : Cx.Hom A A' (RingHom.id R)) : Cx.Hom (sh A) (sh A') (RingHom.id R) where
  f := shFf φ
  comm n x := by
    cases n with
    | zero => exact (map_zero (shFf φ 1)).symm
    | succ n =>
      change -(A'.d n (φ.f n x)) = φ.f (n + 1) (-(A.d n x))
      rw [map_neg, φ.comm]

theorem sh_mem_B {n : ℕ} (x : A.X n) (h : x ∈ A.B n) : (show (sh A).X (n + 1) from x) ∈ (sh A).B (n + 1) := by
  cases n with
  | zero =>
    have e : x = 0 := h
    subst e
    exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨y, rfl⟩ := h
    refine ⟨(-y : A.X n), ?_⟩
    change -(A.d n (-y)) = A.d n y
    rw [map_neg, neg_neg]

theorem mem_B_sh {n : ℕ} (x : (sh A).X (n + 1)) (h : x ∈ (sh A).B (n + 1)) : (show A.X n from x) ∈ A.B n := by
  cases n with
  | zero =>
    obtain ⟨y, rfl⟩ := h
    exact Submodule.zero_mem (A.B 0)
  | succ n =>
    obtain ⟨y, rfl⟩ := h
    refine ⟨-(show A.X n from y), ?_⟩
    change A.d n (-y) = -(A.d n y)
    rw [map_neg]

theorem sh_cocycle {n : ℕ} (x : (sh A).X (n + 1)) (h : (sh A).d (n + 1) x = 0) : A.d n (show A.X n from x) = 0 :=
  neg_eq_zero.1 h

def eZ (A : Cx.{w} R) (n : ℕ) : (sh A).Z (n + 1) →ₗ[R] A.Z n :=
  LinearMap.codRestrict (A.Z n) ((show (sh A).X (n + 1) →ₗ[R] A.X n from LinearMap.id).comp ((sh A).Z (n + 1)).subtype)
    fun z => sh_cocycle z.1 z.2

def eH (A : Cx.{w} R) (n : ℕ) : (sh A).H (n + 1) →ₗ[R] A.H n :=
  Submodule.mapQ _ _ (eZ A n) fun z hz => mem_B_sh z.1 hz

theorem eH_cls (n : ℕ) (x : (sh A).X (n + 1)) (hx : (sh A).d (n + 1) x = 0) :
    eH A n ((sh A).cls x hx) = A.cls (show A.X n from x) (sh_cocycle x hx) := rfl

theorem eH_shF (φ : Cx.Hom A A' (RingHom.id R)) (n : ℕ) (y : (sh A).H (n + 1)) :
    eH A' n ((shF φ).mapH (n + 1) y) = φ.mapH n (eH A n y) := by
  obtain ⟨x, hx, rfl⟩ := cls_surj _ _ y
  rfl

theorem sh_sub {n : ℕ} (h : ∀ m, m + 1 = n → Subsingleton (A.H m)) : Subsingleton ((sh A).H n) := by
  cases n with
  | zero =>
    refine sub_of_mem_B fun x _ => ?_
    have e : x = 0 := Subsingleton.elim (α := PUnit.{w + 1}) _ _
    rw [e]
    exact Submodule.zero_mem _
  | succ m =>
    refine sub_of_mem_B fun x hx => ?_
    exact sh_mem_B _ (mem_B_of_sub (h m rfl) _ (sh_cocycle x hx))

variable {B B' : Cx.{w} R}

def shRf (ρ : ∀ n, A.X n →ₗ[R] B.X (n + 2)) : ∀ n, shX A n →ₗ[R] B.X (n + 1)
  | 0 => 0
  | n + 1 => ρ n

def shR (ρ : ∀ n, A.X n →ₗ[R] B.X (n + 2)) (hρ : ∀ n x, B.d (n + 2) (ρ n x) = ρ (n + 1) (A.d n x)) : AD (sh A) B where
  r := shRf ρ
  anti n x := by
    cases n with
    | zero =>
      change B.d 1 0 + ρ 0 0 = 0
      rw [map_zero, map_zero, add_zero]
    | succ n =>
      change B.d (n + 2) (ρ n x) + ρ (n + 1) (-(A.d n x)) = 0
      rw [hρ, map_neg, add_neg_cancel]

def shHf (η : ∀ n, A.X n →ₗ[R] B.X (n + 1)) : ∀ n, shX A n →ₗ[R] B.X n
  | 0 => 0
  | n + 1 => η n

def shN (ρ : ∀ n, A.X n →ₗ[R] B.X (n + 2)) (hρ : ∀ n x, B.d (n + 2) (ρ n x) = ρ (n + 1) (A.d n x))
    (η : ∀ n, A.X n →ₗ[R] B.X (n + 1)) (hη : ∀ n x, B.d (n + 1) (η n x) + η (n + 1) (A.d n x) = ρ n x) :
    NH (shR ρ hρ) where
  h := shHf η
  eq n x := by
    cases n with
    | zero =>
      change B.d 0 0 - η 0 0 = 0
      rw [map_zero, map_zero, sub_zero]
    | succ n =>
      change B.d (n + 1) (η n x) - η (n + 1) (-(A.d n x)) = ρ n x
      rw [map_neg, sub_neg_eq_add, hη]

end Shift

section Sys

variable {ι : Type} [DecidableEq ι]

theorem cech_d (P : PM.{w} R ι) (n : ℕ) (x : P.cech.X n) (i : Fin (n + 2) → ι) :
    P.cech.d n x i = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • P.res (ent_comp i k.succAbove) (x (i ∘ k.succAbove)) := by
  simp [Cos.d, LinearMap.sum_apply, Finset.sum_apply]

theorem cech_nat (P Q : PM.{w} R ι) (f : ∀ S, P.M S →ₗ[R] Q.M S)
    (hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x)) (n : ℕ) (x : P.cech.X n) :
    Q.cech.d n (fun i => f _ (x i)) = fun i => f _ (P.cech.d n x i) := by
  funext i
  rw [cech_d, cech_d, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, hf]

def prodP (P Q : PM.{w} R ι) : PM.{w} R ι where
  M S := P.M S × Q.M S
  res h := (P.res h).prodMap (Q.res h)
  res_id S h x := Prod.ext (P.res_id S h x.1) (Q.res_id S h x.2)
  res_comp h h' x := Prod.ext (P.res_comp h h' x.1) (Q.res_comp h h' x.2)

theorem d_fst (P Q : PM.{w} R ι) (n : ℕ) (z : (prodP P Q).cech.X n) :
    P.cech.d n (fun i => (z i).1) = fun i => ((prodP P Q).cech.d n z i).1 :=
  cech_nat (prodP P Q) P (fun S => LinearMap.fst R _ _) (fun h x => rfl) n z

theorem d_snd (P Q : PM.{w} R ι) (n : ℕ) (z : (prodP P Q).cech.X n) :
    Q.cech.d n (fun i => (z i).2) = fun i => ((prodP P Q).cech.d n z i).2 :=
  cech_nat (prodP P Q) Q (fun S => LinearMap.snd R _ _) (fun h x => rfl) n z

theorem d_pair (P Q : PM.{w} R ι) (n : ℕ) (x : P.cech.X n) (y : Q.cech.X n) :
    (prodP P Q).cech.d n (fun i => (x i, y i)) = fun i => (P.cech.d n x i, Q.cech.d n y i) := by
  funext i
  exact Prod.ext (congrFun (d_fst P Q n (fun i => (x i, y i))) i).symm (congrFun (d_snd P Q n (fun i => (x i, y i))) i).symm

theorem d_zero (P Q : PM.{w} R ι) (n : ℕ) (z : (prodP P Q).cech.X n) (h : (prodP P Q).cech.d n z = 0) :
    P.cech.d n (fun i => (z i).1) = 0 ∧ Q.cech.d n (fun i => (z i).2) = 0 := by
  rw [d_fst, d_snd, h]
  exact ⟨rfl, rfl⟩

theorem prod_Ex {P Q : PM.{w} R ι} (hP : P.Ex) (hQ : Q.Ex) : (prodP P Q).Ex := by
  obtain ⟨a1, a2, a3, a4⟩ := hP
  obtain ⟨b1, b2, b3, b4⟩ := hQ
  have aug : ∀ x : P.M ∅ × Q.M ∅, (prodP P Q).aug x = fun i => (P.aug x.1 i, Q.aug x.2 i) := fun _ => rfl
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · change (prodP P Q).cech.d 0 ((prodP P Q).aug x) = 0
    rw [aug, d_pair]
    funext i
    exact Prod.ext (congrFun (a1 x.1) i) (congrFun (b1 x.2) i)
  · have h1 : P.aug x.1 = 0 := funext fun i => congrArg Prod.fst (congrFun hx i)
    have h2 : Q.aug x.2 = 0 := funext fun i => congrArg Prod.snd (congrFun hx i)
    exact Prod.ext (a2 x.1 h1) (b2 x.2 h2)
  · obtain ⟨e1, e2⟩ := d_zero P Q 0 y hy
    obtain ⟨x1, h1⟩ := a3 _ e1
    obtain ⟨x2, h2⟩ := b3 _ e2
    refine ⟨(x1, x2), ?_⟩
    rw [one_smul] at h1 h2 ⊢
    rw [aug]
    funext i
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)
  · obtain ⟨e1, e2⟩ := d_zero P Q (n + 1) y hy
    obtain ⟨x1, h1⟩ := a4 n _ e1
    obtain ⟨x2, h2⟩ := b4 n _ e2
    refine ⟨fun i => (x1 i, x2 i), ?_⟩
    rw [one_smul] at h1 h2 ⊢
    refine (d_pair P Q n x1 x2).trans ?_
    funext i
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)

theorem Ex_of_sub (P : PM.{w} R ι) (h : ∀ S, Subsingleton (P.M S)) : P.Ex := by
  have h2 : ∀ n, Subsingleton (P.cech.cx.X n) := fun n =>
    show Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)) from inferInstance
  have h3 := h ∅
  exact ⟨fun x => (h2 _).elim _ _, fun x _ => Subsingleton.elim _ _, fun y _ => ⟨0, (h2 _).elim _ _⟩,
    fun n y _ => ⟨0, (h2 _).elim _ _⟩⟩

def shSy (A : Sy.{w} R ι) : Sy.{w} R ι where
  K S := sh (A.K S)
  res h := shF (A.res h)
  res_id S h n x := by
    cases n with
    | zero => exact Subsingleton.elim (α := PUnit.{w + 1}) _ _
    | succ n => exact A.res_id S h n x
  res_comp h h' n x := by
    cases n with
    | zero => exact Subsingleton.elim (α := PUnit.{w + 1}) _ _
    | succ n => exact A.res_comp h h' n x

theorem shSy_desc {A : Sy.{w} R ι} (hA : A.Desc) : (shSy A).Desc := fun n => by
  cases n with
  | zero => exact Ex_of_sub _ fun S => inferInstanceAs (Subsingleton PUnit.{w + 1})
  | succ n => exact hA n

structure Dat (A B : Sy.{w} R ι) where
  ρ : ∀ S n, (A.K S).X n →ₗ[R] (B.K S).X (n + 2)
  hρ : ∀ S n x, (B.K S).d (n + 2) (ρ S n x) = ρ S (n + 1) ((A.K S).d n x)
  hn : ∀ {S T : Finset ι} (h : S ⊆ T) n x, ρ T n ((A.res h).f n x) = (B.res h).f _ (ρ S n x)

def flatCx (R : Type) [CommRing R] : Cx.{0} R where
  X _ := R
  d _ := 0
  dd _ _ := rfl

def flatSy (R : Type) [CommRing R] (ι : Type) : Sy.{0} R ι where
  K _ := flatCx R
  res _ := ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩
  res_id _ _ _ _ := rfl
  res_comp _ _ _ _ := rfl

def exDat (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] : Dat (flatSy R ι) (flatSy R ι) where
  ρ _ _ := LinearMap.id
  hρ _ _ _ := rfl
  hn _ _ _ := rfl

theorem exDat_ne (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [DecidableEq ι] :
    ∃ x : ((flatSy R ι).K ∅).X 0, (exDat R ι).ρ ∅ 0 x ≠ 0 := ⟨(1 : R), one_ne_zero (α := R)⟩

variable {A B : Sy.{w} R ι}

def Dat.ad (D : Dat A B) (S : Finset ι) : AD (sh (A.K S)) (B.K S) := shR (D.ρ S) (D.hρ S)

theorem Dat.compat (D : Dat A B) {S T : Finset ι} (h : S ⊆ T) (n : ℕ) (x : (sh (A.K S)).X n) :
    (D.ad T).r n ((shF (A.res h)).f n x) = (B.res h).f (n + 1) ((D.ad S).r n x) := by
  cases n with
  | zero => exact (map_zero ((B.res h).f 1)).symm
  | succ n => exact D.hn h n x

def Dat.sy (D : Dat A B) : Sy.{w} R ι where
  K S := cone (D.ad S)
  res h := coneHom _ _ (shF (A.res h)) (B.res h) (D.compat h)
  res_id S h n x := Prod.ext (B.res_id S h n x.1) ((shSy A).res_id S h n x.2)
  res_comp h h' n x := Prod.ext (B.res_comp h h' n x.1) ((shSy A).res_comp h h' n x.2)

def Dat.m (D : Dat A B) : D.sy.Hom (shSy A) where
  φ S := pr (D.ad S)
  nat h n x := rfl

theorem Dat.desc (D : Dat A B) (hA : A.Desc) (hB : B.Desc) : D.sy.Desc := fun n =>
  prod_Ex (P := B.term n) (Q := (shSy A).term n) (hB n) (shSy_desc hA n)

end Sys

theorem coneKillOf : ConeKillOf := by
  intro hs
  unfold ConeKill
  intro R _ ι _ A B a hA hB oA oB ρ η hρ hρn hηn hη lam hlamn hlam n x hx
  let D : Dat A B := ⟨ρ, hρ, hρn⟩
  let N : ∀ (α : ι) (S : Finset ι), α ∈ S → NH (D.ad S) := fun α S hS => shN (ρ S) (hρ S) (η α S hS) (hη α S hS)
  let l : ∀ (α : ι) (S : Finset ι), α ∈ S → ((sh (A.K S)).H (a + 1) →ₗ[R] (B.K S).H (a + 1)) :=
    fun α S hS => (lam α S hS).comp (eH (A.K S) a)
  have hind : ∀ (S : Finset ι) (α α' : ι) (hS : α ∈ S) (hS' : α' ∈ S),
      secM (D.ad S) (N α S hS) (a + 1) (l α S hS) = secM (D.ad S) (N α' S hS') (a + 1) (l α' S hS') := by
    intro S α α' hS hS'
    exact secM_eq _ _ _ _ _ _ fun x hx hz => hlam α α' S hS hS' x (sh_cocycle x hx) hz
  let σ : ∀ S : Finset ι, S.Nonempty → (((shSy A).K S).H (a + 1) →ₗ[R] (D.sy.K S).H (a + 1)) :=
    fun S hS => secM (D.ad S) (N hS.choose S hS.choose_spec) (a + 1) (l _ S hS.choose_spec)
  have oneS : (shSy A).One (a + 1) := fun S hS j hj => sh_sub fun m hm => oA S hS m (by omega)
  have oneC : D.sy.One (a + 1) := fun S hS j hj =>
    cone_one (D.ad S) (N _ S hS.choose_spec) j (oB S hS j hj) (oneS S hS j hj)
  have hsec : ∀ S hS x, (D.m.φ S).mapH (a + 1) (σ S hS x) = x := fun S hS x => pr_secM _ _ _ _ x
  have hnat : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT x,
      σ T hT (((shSy A).res h).mapH (a + 1) x) = (D.sy.res h).mapH (a + 1) (σ S hS x) := by
    intro S T h hS hT x
    have hα := hS.choose_spec
    have e := hind T hT.choose hS.choose hT.choose_spec (h hα)
    refine (congrArg (fun f => f (((shSy A).res h).mapH (a + 1) x)) e).trans ?_
    refine secM_nat (D.ad S) (D.ad T) (shF (A.res h)) (B.res h) (D.compat h) (N _ S hα) (N _ T (h hα)) (a + 1) (l _ S hα)
      (l _ T (h hα)) (fun x => hηn _ h hα a x) (fun y => ?_) x
    change lam _ T _ (eH (A.K T) a ((shF (A.res h)).mapH (a + 1) y)) = _
    rw [eH_shF]
    exact hlamn _ h hα _
  have surj := hs R ι D.sy (shSy A) D.m (a + 1) (D.desc hA hB) (shSy_desc hA) oneC oneS σ hsec hnat (n + 1)
  refine kill (D.ad ∅) (n + 1) surj x ?_
  change -((A.K ∅).d n x) = 0
  rw [hx, neg_zero]

end GlobalTheory.CompanionTheory.ConeKillC
