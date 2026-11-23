import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.OneSurjC

universe w w'

variable {R : Type} [CommRing R]

section Abs

variable {K : DCx.{w} R}

def Vn (K : DCx.{w} R) (t : ℕ) (x : ∀ p q, K.X p q) : Prop := ∀ p q, t ≤ q → x p q = 0

def Pv (K : DCx.{w} R) (n : ℕ) (x : ∀ p q, K.X p q) : Prop := ∀ p q, p + q + 1 ≠ n → x p q = 0

theorem Vn.mono {t : ℕ} {x : ∀ p q, K.X p q} (h : Vn K t x) : Vn K (t + 1) x := fun p q hq => h p q (by omega)

theorem Vn.add {t : ℕ} {x y : ∀ p q, K.X p q} (h : Vn K t x) (h' : Vn K t y) : Vn K t (x + y) := fun p q hq => by
  rw [Pi.add_apply, Pi.add_apply, h p q hq, h' p q hq, add_zero]

theorem Vn.sub {t : ℕ} {x y : ∀ p q, K.X p q} (h : Vn K t x) (h' : Vn K t y) : Vn K t (x - y) := fun p q hq => by
  rw [Pi.sub_apply, Pi.sub_apply, h p q hq, h' p q hq, sub_zero]

theorem Pv.add {n : ℕ} {x y : ∀ p q, K.X p q} (h : Pv K n x) (h' : Pv K n y) : Pv K n (x + y) := fun p q hq => by
  rw [Pi.add_apply, Pi.add_apply, h p q hq, h' p q hq, add_zero]

theorem Pv.sub {n : ℕ} {x y : ∀ p q, K.X p q} (h : Pv K n x) (h' : Pv K n y) : Pv K n (x - y) := fun p q hq => by
  rw [Pi.sub_apply, Pi.sub_apply, h p q hq, h' p q hq, sub_zero]

theorem Pv.zero (n : ℕ) : Pv K n 0 := fun _ _ _ => rfl

theorem Vn.zero (t : ℕ) : Vn K t 0 := fun _ _ _ => rfl

theorem Pv.mem {m : ℕ} {x : ∀ p q, K.X p q} (h : Pv K (m + 1) x) : x ∈ K.T m := fun p q hq => h p q (by omega)

theorem Pv.D_mem {n : ℕ} {x : ∀ p q, K.X p q} (h : Pv K n x) : K.D x ∈ K.T n := by
  cases n with
  | zero =>
    have : x = 0 := by
      funext p q
      exact h p q (by omega)
    rw [this, map_zero]
    exact Submodule.zero_mem _
  | succ m => exact K.D_mem m x h.mem

theorem sgl_mem (p q : ℕ) (x : K.X p q) : K.sgl p q x ∈ K.T (p + q) := fun a b hab => K.sgl_ne x (by omega)

theorem kill (p a : ℕ) (z : K.X p a) (hz : z ∈ (K.col p).B a) :
    ∃ g, Pv K (p + a) g ∧ Vn K a g ∧ Vn K a (K.D g - K.sgl p a z) := by
  cases a with
  | zero =>
    have h0 : z = 0 := hz
    subst h0
    refine ⟨0, Pv.zero _, Vn.zero _, ?_⟩
    rw [map_zero, map_zero, sub_zero]
    exact Vn.zero _
  | succ a =>
    obtain ⟨u, rfl⟩ := hz
    refine ⟨(-1 : ℤ) ^ p • K.sgl p a u, fun p' q h => ?_, fun p' q h => ?_, fun p' q h => ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega), smul_zero]
    · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega), smul_zero]
    · have e : K.D ((-1 : ℤ) ^ p • K.sgl p a u) = (-1 : ℤ) ^ p • K.sgl (p + 1) a (K.dh p a u) + K.sgl p (a + 1) (K.dv p a u) := by
        rw [map_zsmul, K.D_sgl, smul_add, smul_smul, ← mul_pow]
        simp
      change (K.D ((-1 : ℤ) ^ p • K.sgl p a u) - K.sgl p (a + 1) (K.dv p a u)) p' q = 0
      rw [e, add_sub_cancel_right, Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega), smul_zero]

theorem cut {n a p : ℕ} (hn : p + a = n) {z : ∀ p q, K.X p q} (hz : z ∈ K.T n) (hs : Vn K (a + 1) z) :
    Vn K a (z - K.sgl p a (z p a)) := fun p' q h => by
  rw [Pi.sub_apply, Pi.sub_apply]
  by_cases h1 : p' = p ∧ q = a
  · obtain ⟨rfl, rfl⟩ := h1
    rw [K.sgl_self, sub_self]
  · rw [K.sgl_ne _ (by omega), sub_zero]
    by_cases h2 : q = a
    · subst h2
      exact hz _ _ (by omega)
    · exact hs _ _ (by omega)

theorem dv_top {t : ℕ} {y : ∀ p q, K.X p q} (hD : K.D y = 0) (hs : Vn K (t + 1) y) (p : ℕ) : K.dv p t (y p t) = 0 := by
  have h := congrFun (congrFun hD p) (t + 1)
  rw [K.D_apply] at h
  have h1 : K.Dh y p (t + 1) = 0 := by
    cases p with
    | zero => rfl
    | succ p =>
      change K.dh p (t + 1) (y p (t + 1)) = 0
      rw [hs _ _ le_rfl, map_zero]
  rw [h1, zero_add] at h
  have h2 : (-1 : ℤ) ^ p • K.dv p t (y p t) = 0 := h
  have h3 := congrArg (fun v => (-1 : ℤ) ^ p • v) h2
  simpa [smul_smul, ← mul_pow] using h3

theorem step {n t : ℕ} {x : ∀ p q, K.X p q} (hx : x ∈ K.T n) (hD : K.D x = 0) (hs : Vn K (t + 1) x)
    (hex : ∀ p (y : K.X p t), K.dv p t y = 0 → y ∈ (K.col p).B t) :
    ∃ w, Pv K n w ∧ Vn K t w ∧ Vn K t (x - K.D w) := by
  by_cases h : t ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + t := ⟨n - t, by omega⟩
    obtain ⟨g, h1, h2, h3⟩ := kill p t (x p t) (hex p _ (dv_top hD hs p))
    refine ⟨g, h1, h2, ?_⟩
    have e : x - K.D g = (x - K.sgl p t (x p t)) - (K.D g - K.sgl p t (x p t)) := by abel
    rw [e]
    exact (cut rfl hx hs).sub h3
  · refine ⟨0, Pv.zero _, Vn.zero _, ?_⟩
    rw [map_zero, sub_zero]
    exact fun p q hq => hx p q (by omega)

theorem DD' (w : ∀ p q, K.X p q) : K.D (K.D w) = 0 := K.DD w

theorem down (t : ℕ) (hex : ∀ s < t, ∀ p (y : K.X p s), K.dv p s y = 0 → y ∈ (K.col p).B s) {n : ℕ} {x : ∀ p q, K.X p q}
    (hx : x ∈ K.T n) (hD : K.D x = 0) (hs : Vn K t x) : ∃ w, Pv K n w ∧ Vn K t w ∧ K.D w = x := by
  induction t generalizing x with
  | zero =>
    refine ⟨0, Pv.zero _, Vn.zero _, ?_⟩
    rw [map_zero]
    funext p q
    exact (hs p q (Nat.zero_le _)).symm
  | succ t ih =>
    obtain ⟨w₁, h1, h2, h3⟩ := step hx hD hs (hex t (by omega))
    obtain ⟨w₂, k1, k2, k3⟩ := ih (fun s hs' => hex s (by omega)) (Submodule.sub_mem _ hx h1.D_mem)
      (by rw [map_sub, hD, DD', sub_zero]) h3
    refine ⟨w₁ + w₂, h1.add k1, (h2.add k2).mono, ?_⟩
    rw [map_add, k3]
    abel

theorem up (a : ℕ) (hex : ∀ s, a < s → ∀ p (y : K.X p s), K.dv p s y = 0 → y ∈ (K.col p).B s) {n : ℕ} (k : ℕ)
    {x : ∀ p q, K.X p q} (hx : x ∈ K.T n) (hD : K.D x = 0) (hs : Vn K (a + 1 + k) x) :
    ∃ x' w, x' ∈ K.T n ∧ K.D x' = 0 ∧ Vn K (a + 1) x' ∧ Pv K n w ∧ x - x' = K.D w := by
  induction k generalizing x with
  | zero => exact ⟨x, 0, hx, hD, hs, Pv.zero _, by rw [map_zero, sub_self]⟩
  | succ k ih =>
    obtain ⟨w₁, h1, h2, h3⟩ := step (t := a + 1 + k) hx hD hs (hex _ (by omega))
    obtain ⟨x', w₂, k1, k2, k3, k4, k5⟩ := ih (Submodule.sub_mem _ hx h1.D_mem) (by rw [map_sub, hD, DD', sub_zero]) h3
    refine ⟨x', w₁ + w₂, k1, k2, k3, h1.add k4, ?_⟩
    rw [map_add, ← k5]
    abel

theorem lift {a p : ℕ} (hex : ∀ s < a, ∀ p (y : K.X p s), K.dv p s y = 0 → y ∈ (K.col p).B s) (x₀ : K.X p a)
    (h1 : K.dv p a x₀ = 0) (h2 : K.dh p a x₀ ∈ (K.col (p + 1)).B a) :
    ∃ x, x ∈ K.T (p + a) ∧ K.D x = 0 ∧ Vn K (a + 1) x ∧ x p a = x₀ := by
  obtain ⟨g, g1, g2, g3⟩ := kill (p + 1) a _ h2
  have hDe : K.D (K.sgl p a x₀) = K.sgl (p + 1) a (K.dh p a x₀) := by
    rw [K.D_sgl, h1, map_zero, smul_zero, add_zero]
  have hm : K.D (K.sgl p a x₀) - K.D g ∈ K.T (p + 1 + a) :=
    Submodule.sub_mem _ (by rw [hDe]; exact sgl_mem _ _ _) g1.D_mem
  have hv : Vn K a (K.D (K.sgl p a x₀) - K.D g) := by
    rw [hDe]
    have := (Vn.zero a).sub g3
    rw [zero_sub, neg_sub] at this
    exact this
  obtain ⟨w, w1, w2, w3⟩ := down a hex hm (by rw [map_sub, DD', DD', sub_zero]) hv
  refine ⟨K.sgl p a x₀ - g - w, ?_, ?_, fun p' q h => ?_, ?_⟩
  · refine Submodule.sub_mem _ (Submodule.sub_mem _ (sgl_mem _ _ _) fun a b h => g1 a b (by omega)) fun a b h => w1 a b (by omega)
  · rw [map_sub, map_sub, w3]
    abel
  · rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, K.sgl_ne _ (by omega), g2 _ _ (by omega), w2 _ _ (by omega)]
    simp
  · rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, K.sgl_self, g2 _ _ le_rfl, w2 _ _ le_rfl]
    simp

theorem dh_bd {y : ∀ p q, K.X p q} (hD : K.D y = 0) (p a : ℕ) : K.dh p a (y p a) ∈ (K.col (p + 1)).B a := by
  cases a with
  | zero =>
    have h := congrFun (congrFun hD (p + 1)) 0
    rw [K.D_apply] at h
    have h0 : K.Dv y (p + 1) 0 = 0 := rfl
    rw [h0, smul_zero, add_zero] at h
    exact h
  | succ a =>
    have h := congrFun (congrFun hD (p + 1)) (a + 1)
    rw [K.D_apply] at h
    have h' : K.dh p (a + 1) (y p (a + 1)) + (-1 : ℤ) ^ (p + 1) • K.dv (p + 1) a (y (p + 1) a) = 0 := h
    refine ⟨-((-1 : ℤ) ^ (p + 1) • y (p + 1) a), ?_⟩
    change K.dv (p + 1) a (-((-1 : ℤ) ^ (p + 1) • y (p + 1) a)) = _
    rw [map_neg, map_zsmul]
    exact (eq_neg_of_add_eq_zero_left h').symm

theorem prevB {n : ℕ} (u : K.tot.X n) (w : ∀ p q, K.X p q) (hw : Pv K n w) (h : u.1 = K.D w) : u ∈ K.tot.B n := by
  cases n with
  | zero =>
    have h0 : w = 0 := by
      funext p q
      exact hw p q (by omega)
    rw [h0, map_zero] at h
    exact Subtype.ext h
  | succ m => exact ⟨⟨w, hw.mem⟩, Subtype.ext h.symm⟩

theorem surj {L : DCx.{w'} R} (φ : DCx.Hom K L (RingHom.id R)) (a : ℕ)
    (hK : ∀ s, s ≠ a → ∀ p (y : K.X p s), K.dv p s y = 0 → y ∈ (K.col p).B s)
    (hL : ∀ s, s ≠ a → ∀ p (y : L.X p s), L.dv p s y = 0 → y ∈ (L.col p).B s)
    (S : ∀ p (y : L.X p a), L.dv p a y = 0 → L.dh p a y ∈ (L.col (p + 1)).B a →
      ∃ x : K.X p a, K.dv p a x = 0 ∧ K.dh p a x ∈ (K.col (p + 1)).B a ∧ φ.f p a x - y ∈ (L.col p).B a)
    (n : ℕ) : Function.Surjective (φ.tot.mapH n) := by
  intro c
  obtain ⟨y, hy, rfl⟩ := (P.cls_surj L.tot n).1 c
  have hyD : L.D y.1 = 0 := congrArg Subtype.val hy
  obtain ⟨y', w, t1, t2, t3, t4, t5⟩ := up a (fun s hs => hL s (by omega)) n y.2 hyD (fun p q h => y.2 p q (by omega))
  by_cases hn : n < a
  · have hv : Vn L a y' := fun p q h => t1 p q (by omega)
    obtain ⟨w', u1, u2, u3⟩ := down a (fun s hs => hL s (by omega)) t1 t2 hv
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    rw [(P.cls_surj L.tot n).2.1]
    exact prevB y (w + w') (t4.add u1) (by rw [map_add, u3, ← t5]; abel)
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + a := ⟨n - a, by omega⟩
    obtain ⟨x₀, s1, s2, s3⟩ := S p _ (dv_top t2 t3 p) (dh_bd t2 p a)
    obtain ⟨x, x1, x2, x3, x4⟩ := lift (fun s hs => hK s (by omega)) x₀ s1 s2
    let X : K.tot.X (p + a) := ⟨x, x1⟩
    have hX : K.tot.d (p + a) X = 0 := Subtype.ext x2
    have hb : L.tot.d _ (φ.tot.f _ X) = 0 := by rw [φ.tot.comm, hX, map_zero]
    refine ⟨K.tot.cls X hX, ?_⟩
    rw [P.mapH_cls φ.tot _ X hX hb, (P.cls_surj L.tot _).2.2.1]
    obtain ⟨z, hz⟩ : ∃ z, z = (φ.tot.f _ X).1 - y' := ⟨_, rfl⟩
    have hz1 : z ∈ L.T (p + a) := hz ▸ Submodule.sub_mem _ (φ.tot.f _ X).2 t1
    have hzD : L.D z = 0 := by
      rw [hz, map_sub, t2, sub_zero]
      exact congrArg Subtype.val hb
    have hzv : Vn L (a + 1) z := fun p' q h => by
      rw [hz]
      change φ.f p' q (x p' q) - y' p' q = 0
      rw [x3 p' q h, t3 p' q h, map_zero, sub_zero]
    have hzp : z p a = φ.f p a x₀ - y' p a := by
      rw [hz]
      change φ.f p a (x p a) - y' p a = _
      rw [x4]
    obtain ⟨g, g1, g2, g3⟩ := kill p a (z p a) (hzp ▸ s3)
    have hv : Vn L a (z - L.D g) := by
      have e : z - L.D g = (z - L.sgl p a (z p a)) - (L.D g - L.sgl p a (z p a)) := by abel
      rw [e]
      exact (cut rfl hz1 hzv).sub g3
    obtain ⟨w', u1, u2, u3⟩ := down a (fun s hs => hL s (by omega)) (Submodule.sub_mem _ hz1 g1.D_mem)
      (by rw [map_sub, hzD, DD', sub_zero]) hv
    refine prevB _ (g + w' - w) ((g1.add u1).sub t4) ?_
    rw [map_sub, map_add, u3, ← t5]
    change (φ.tot.f _ X).1 - y.1 = _
    have e1 : (φ.tot.f _ X).1 = z + y' := by rw [hz]; abel
    rw [e1]
    abel

end Abs

section App

variable {ι : Type} [DecidableEq ι]

theorem ent_ne {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty := ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

abbrev colK (A : Sy.{w} R ι) (p : ℕ) : Cx.{w} R where
  X q := ∀ i : Fin (p + 1) → ι, (A.K (ent i)).X q
  d q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  dd q x := by
    funext i
    exact (A.K (ent i)).dd q (x i)

abbrev cc (A : Sy.{w} R ι) : CosCx.{w} R where
  K p := colK A p
  δ p k := ⟨fun q => (A.term q).cech.δ p k, fun q x => by
    funext t
    exact (A.res (ent_comp t k.succAbove)).comm q (x (t ∘ k.succAbove))⟩
  rel p j i q x := (A.term q).cech.rel p j i x

def augR (A : Sy.{w} R ι) (h : A.Desc) : DCx.AugRow (A.K ∅) (cc A).dcx where
  ε q := (A.term q).aug
  hε q x := (h q).1 x
  comm q x := by
    funext i
    exact (A.res (Finset.empty_subset _)).comm q x

def hm {A : Sy.{w} R ι} {B : Sy.{w'} R ι} (m : A.Hom B) : DCx.Hom (cc A).dcx (cc B).dcx (RingHom.id R) where
  f p q := LinearMap.pi fun i => ((m.φ (ent i)).f q).comp (LinearMap.proj i)
  ch p q x := by
    change ((cc B).cos q).d p _ = _
    change _ = (LinearMap.pi fun i => ((m.φ (ent i)).f q).comp (LinearMap.proj i)) (((cc A).cos q).d p x)
    rw [Cos.d_apply, Cos.d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    funext t
    exact (m.nat (ent_comp t k.succAbove) q (x (t ∘ k.succAbove))).symm
  cv p q x := by
    funext i
    exact (m.φ (ent i)).comm q (x i)

theorem piB (A : Sy.{w} R ι) (p s : ℕ) (y : (colK A p).X s) : y ∈ (colK A p).B s ↔ ∀ i, y i ∈ (A.K (ent i)).B s := by
  cases s with
  | zero =>
    constructor
    · intro h i
      have h0 : y = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      exact funext h
  | succ s =>
    constructor
    · rintro ⟨u, rfl⟩ i
      exact ⟨u i, rfl⟩
    · intro h
      choose u hu using h
      exact ⟨u, funext hu⟩

theorem colEx (A : Sy.{w} R ι) {a : ℕ} (oA : A.One a) (s : ℕ) (hs : s ≠ a) (p : ℕ) (y : (cc A).dcx.X p s)
    (hy : (cc A).dcx.dv p s y = 0) : y ∈ ((cc A).dcx.col p).B s := by
  refine (piB A p s y).2 fun i => ?_
  have hi : (A.K (ent i)).d s (y i) = 0 := congrFun hy i
  have := oA (ent i) (ent_ne i) s hs
  exact ((P.cls_surj (A.K (ent i)) s).2.1 _ hi).1 (Subsingleton.elim _ _)

theorem cls_sum {C : Cx.{w} R} {a : ℕ} {κ : Type} [Fintype κ] (c : κ → ℤ) (v : κ → C.X a) (hv : ∀ k, C.d a (v k) = 0)
    (h : C.d a (∑ k, c k • v k) = 0) : C.cls (∑ k, c k • v k) h = ∑ k, c k • C.cls (v k) (hv k) := by
  have e : (⟨∑ k, c k • v k, h⟩ : C.Z a) = ∑ k, c k • (⟨v k, hv k⟩ : C.Z a) := by
    apply Subtype.ext
    simp
  unfold Cx.cls
  rw [e]
  change Submodule.mkQ _ _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_zsmul _ _ _

def cl (A : Sy.{w} R ι) (a p : ℕ) (x : (colK A p).X a) (hx : ∀ i, (A.K (ent i)).d a (x i) = 0) : (A.coh a).cech.X p :=
  fun i => (A.K (ent i)).cls (x i) (hx i)

theorem cl_dh (A : Sy.{w} R ι) (a p : ℕ) (x : (colK A p).X a) (hx : ∀ i, (A.K (ent i)).d a (x i) = 0)
    (h' : ∀ t, (A.K (ent t)).d a (((A.term a).cech.d p x) t) = 0) :
    cl A a (p + 1) ((A.term a).cech.d p x) h' = (A.coh a).cech.d p (cl A a p x hx) := by
  funext t
  have hv : ∀ k : Fin (p + 2), (A.K (ent t)).d a ((A.res (ent_comp t k.succAbove)).f a (x (t ∘ k.succAbove))) = 0 := fun k => by
    rw [(A.res _).comm, hx, map_zero]
  have e1 : ((A.term a).cech.d p x) t = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (A.res (ent_comp t k.succAbove)).f a (x (t ∘ k.succAbove)) := by
    rw [Cos.d_apply, Finset.sum_apply]
    rfl
  have e2 : (A.coh a).cech.d p (cl A a p x hx) t = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (A.K (ent t)).cls _ (hv k) := by
    rw [Cos.d_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply]
    congr 1
  rw [e2]
  change (A.K (ent t)).cls _ (h' t) = _
  simp only [e1]
  exact cls_sum _ _ hv _

end App

section Fin

variable {ι : Type} [DecidableEq ι]

def sc {A : Sy.{w} R ι} {B : Sy.{w'} R ι} {a : ℕ} (σ : ∀ S : Finset ι, S.Nonempty → ((B.K S).H a →ₗ[R] (A.K S).H a)) (p : ℕ)
    (g : (B.coh a).cech.X p) : (A.coh a).cech.X p := fun i => σ (ent i) (ent_ne i) (g i)

theorem sc_d {A : Sy.{w} R ι} {B : Sy.{w'} R ι} {a : ℕ} (σ : ∀ S : Finset ι, S.Nonempty → ((B.K S).H a →ₗ[R] (A.K S).H a))
    (h2 : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT x, σ T hT ((B.res h).mapH a x) = (A.res h).mapH a (σ S hS x))
    (p : ℕ) (g : (B.coh a).cech.X p) : sc σ (p + 1) ((B.coh a).cech.d p g) = (A.coh a).cech.d p (sc σ p g) := by
  funext t
  rw [Cos.d_apply, Cos.d_apply]
  change σ (ent t) (ent_ne t) ((∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (B.coh a).cech.δ p k g) t) = _
  rw [Finset.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, map_zsmul]
  congr 1
  exact h2 (ent_comp t k.succAbove) (ent_ne _) (ent_ne t) (g _)

theorem sprop {A : Sy.{w} R ι} {B : Sy.{w'} R ι} (m : A.Hom B) (a : ℕ)
    (σ : ∀ S : Finset ι, S.Nonempty → ((B.K S).H a →ₗ[R] (A.K S).H a))
    (h1 : ∀ S hS x, (m.φ S).mapH a (σ S hS x) = x)
    (h2 : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT x, σ T hT ((B.res h).mapH a x) = (A.res h).mapH a (σ S hS x))
    (p : ℕ) (y : (cc B).dcx.X p a) (hy : (cc B).dcx.dv p a y = 0)
    (hb : (cc B).dcx.dh p a y ∈ ((cc B).dcx.col (p + 1)).B a) :
    ∃ x : (cc A).dcx.X p a, (cc A).dcx.dv p a x = 0 ∧ (cc A).dcx.dh p a x ∈ ((cc A).dcx.col (p + 1)).B a ∧
      (hm m).f p a x - y ∈ ((cc B).dcx.col p).B a := by
  have hyi : ∀ i, (B.K (ent i)).d a (y i) = 0 := fun i => congrFun hy i
  choose x hx hxe using fun i : Fin (p + 1) → ι =>
    (P.cls_surj (A.K (ent i)) a).1 (σ _ (ent_ne i) ((B.K _).cls (y i) (hyi i)))
  have hvx : (cc A).dcx.dv p a x = 0 := funext hx
  have hdx : (cc A).dcx.dv (p + 1) a ((cc A).dcx.dh p a x) = 0 := by
    rw [← (cc A).dcx.hv, hvx, map_zero]
  have hdy : (cc B).dcx.dv (p + 1) a ((cc B).dcx.dh p a y) = 0 := by
    rw [← (cc B).dcx.hv, hy, map_zero]
  refine ⟨x, hvx, ?_, ?_⟩
  · refine (piB A (p + 1) a _).2 fun t => ?_
    have c1 := cl_dh A a p x hx (fun t => congrFun hdx t)
    have c2 := cl_dh B a p y hyi (fun t => congrFun hdy t)
    have cx : cl A a p x hx = sc σ p (cl B a p y hyi) := funext fun i => (hxe i).symm
    have z0 : cl B a (p + 1) ((B.term a).cech.d p y) (fun t => congrFun hdy t) = 0 :=
      funext fun t => ((P.cls_surj _ a).2.1 _ _).2 ((piB B (p + 1) a _).1 hb t)
    have z1 : sc σ (p + 1) (0 : (B.coh a).cech.X (p + 1)) = 0 := funext fun t => map_zero _
    have z2 : cl A a (p + 1) ((A.term a).cech.d p x) (fun t => congrFun hdx t) = 0 := by
      rw [c1, cx, ← sc_d σ h2, ← c2, z0, z1]
    exact ((P.cls_surj _ a).2.1 _ _).1 (congrFun z2 t)
  · refine (piB B p a _).2 fun i => ?_
    have h := h1 (ent i) (ent_ne i) ((B.K _).cls (y i) (hyi i))
    rw [hxe i, P.mapH_cls (m.φ (ent i)) a (x i) (hx i) (by rw [(m.φ _).comm, hx, map_zero])] at h
    exact ((P.cls_surj _ a).2.2.1 _ _ _ _).1 h

theorem surjS {A : Sy.{w} R ι} {B : Sy.{w'} R ι} (m : A.Hom B) (a : ℕ) (hA : A.Desc) (hB : B.Desc) (oA : A.One a) (oB : B.One a)
    (σ : ∀ S : Finset ι, S.Nonempty → ((B.K S).H a →ₗ[R] (A.K S).H a))
    (h1 : ∀ S hS x, (m.φ S).mapH a (σ S hS x) = x)
    (h2 : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT x, σ T hT ((B.res h).mapH a x) = (A.res h).mapH a (σ S hS x))
    (n : ℕ) : Function.Surjective ((m.φ ∅).mapH n) := by
  intro b
  have eA := P.dc_row (augR A hA) 1 (fun q => hA q) n
  have eB := P.dc_row (augR B hB) 1 (fun q => hB q) n
  have ht := surj (hm m) a (colEx A oA) (colEx B oB) (sprop m a σ h1 h2) n
  have hc : ∀ c : (A.K ∅).H n, (augR B hB).edge.mapH n ((m.φ ∅).mapH n c) =
      (hm m).tot.mapH n ((augR A hA).edge.mapH n c) := by
    intro c
    obtain ⟨u, hu, rfl⟩ := (P.cls_surj _ n).1 c
    have hm1 : (B.K ∅).d n ((m.φ ∅).f n u) = 0 := by rw [(m.φ ∅).comm, hu, map_zero]
    have he1 : (cc A).dcx.tot.d n ((augR A hA).edge.f n u) = 0 := by rw [(augR A hA).edge.comm, hu, map_zero]
    have he2 : (cc B).dcx.tot.d n ((augR B hB).edge.f n ((m.φ ∅).f n u)) = 0 := by
      rw [(augR B hB).edge.comm, hm1, map_zero]
    have he3 : (cc B).dcx.tot.d n ((hm m).tot.f n ((augR A hA).edge.f n u)) = 0 := by
      rw [(hm m).tot.comm, he1, map_zero]
    have e : (augR B hB).edge.f n ((m.φ ∅).f n u) = (hm m).tot.f n ((augR A hA).edge.f n u) := by
      refine Subtype.ext (funext fun p => funext fun q => ?_)
      change (cc B).dcx.sgl 0 n ((B.term n).aug ((m.φ ∅).f n u)) p q = (hm m).f p q ((cc A).dcx.sgl 0 n ((A.term n).aug u) p q)
      by_cases h : p = 0 ∧ q = n
      · obtain ⟨rfl, rfl⟩ := h
        rw [DCx.sgl_self, DCx.sgl_self]
        funext i
        exact (m.nat (Finset.empty_subset _) _ u).symm
      · rw [DCx.sgl_ne _ _ (by omega), DCx.sgl_ne _ _ (by omega), map_zero]
    rw [P.mapH_cls (m.φ ∅) n u hu hm1, P.mapH_cls _ n _ hm1 he2, P.mapH_cls _ n u hu he1, P.mapH_cls _ n _ he1 he3]
    simp only [e]
  obtain ⟨c₁, hc₁⟩ := ht ((augR B hB).edge.mapH n b)
  obtain ⟨b', hb'⟩ := eA.2 c₁
  rw [one_pow, one_smul] at hb'
  refine ⟨b', ?_⟩
  have h0 : (augR B hB).edge.mapH n ((m.φ ∅).mapH n b' - b) = 0 := by
    rw [map_sub, hc, hb', hc₁, sub_self]
  have h3 := eB.1 _ h0
  rw [one_pow, one_smul] at h3
  exact sub_eq_zero.1 h3

end Fin

theorem oneSurj : OneSurj := by
  intro R _ ι _ A B m a hA hB oA oB σ h1 h2 n
  exact surjS m a hA hB oA oB σ h1 (fun h => h2 h) n

end GlobalTheory.CompanionTheory.OneSurjC
