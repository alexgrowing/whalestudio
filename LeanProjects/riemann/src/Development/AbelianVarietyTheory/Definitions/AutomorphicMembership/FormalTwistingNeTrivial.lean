import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.Vert

namespace GlobalTheory.FormalPic

section Iso

variable {X Y : Scheme.{0}} {A B C : LB X}

theorem isGen_iso_iff (u : LB.Iso A B) : u.IsGen ↔ ∀ (x : X) (p q : B.ι × A.ι), x ∈ B.U p.1 ⊓ A.U p.2 → x ∈ B.U q.1 ⊓ A.U q.2 →
    gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2) (u.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x (B.U q.1 ⊓ A.U q.2) (u.s q) := by
  refine (isGen_iff_germ u).trans (forall₃_congr fun x p q => forall₂_congr fun hp hq => ?_)
  rw [gm_div' B A (𝟙 X) x p q hp hq]
  rfl

theorem gm_congr {U V : X.Opens} {a : Γ(X, U)ˣ} {b : Γ(X, V)ˣ} {W : X.Opens} {c : Γ(X, W)ˣ}
    (h : ∀ x ∈ U ⊓ V ⊓ W, gm (𝟙 X) x U a = gm (𝟙 X) x V b * gm (𝟙 X) x W c) (f : Y ⟶ X) (y : Y)
    (hy : f y ∈ U ⊓ V ⊓ W) : gm f y U a = gm f y V b * gm f y W c := by
  have e : res (inf_le_left.trans inf_le_left : U ⊓ V ⊓ W ≤ U) a =
      res (inf_le_left.trans inf_le_right : U ⊓ V ⊓ W ≤ V) b * res (inf_le_right : U ⊓ V ⊓ W ≤ W) c :=
    unit_ext fun x hx => by rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]; exact h x hx
  have := congrArg (gm f y _) e
  rwa [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy] at this

theorem exists_trans (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) {u : LB.Iso A B} {v : LB.Iso B C} (hu : u.IsGen)
    (hv : v.IsGen) : ∃ w : LB.Iso A C, w.IsGen ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (a : A.ι) (b : B.ι) (c : C.ι),
      f y ∈ A.U a → f y ∈ B.U b → f y ∈ C.U c → gm f y (C.U c ⊓ A.U a) (w.s (c, a)) =
        gm f y (C.U c ⊓ B.U b) (v.s (c, b)) * gm f y (B.U b ⊓ A.U a) (u.s (b, a)) := by
  rw [isGen_iso_iff] at hu hv
  have glue : ∀ (c : C.ι) (a : A.ι), ∃ s : Γ(X, C.U c ⊓ A.U a)ˣ, ∀ (x : X) (b : B.ι), x ∈ A.U a → x ∈ B.U b → x ∈ C.U c →
      gm (𝟙 X) x _ s = gm (𝟙 X) x (C.U c ⊓ B.U b) (v.s (c, b)) * gm (𝟙 X) x (B.U b ⊓ A.U a) (u.s (b, a)) := by
    intro c a
    have l₁ : ∀ b, C.U c ⊓ A.U a ⊓ B.U b ≤ C.U c ⊓ B.U b := fun b x hx => ⟨hx.1.1, hx.2⟩
    have l₂ : ∀ b, C.U c ⊓ A.U a ⊓ B.U b ≤ B.U b ⊓ A.U a := fun b x hx => ⟨hx.2, hx.1.2⟩
    have val : ∀ b, ∀ x ∈ C.U c ⊓ A.U a ⊓ B.U b, gm (𝟙 X) x _ (res (l₁ b) (v.s (c, b)) * res (l₂ b) (u.s (b, a))) =
        gm (𝟙 X) x (C.U c ⊓ B.U b) (v.s (c, b)) * gm (𝟙 X) x (B.U b ⊓ A.U a) (u.s (b, a)) := fun b x hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _) (gm_res _ x _ hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U c ⊓ A.U a) (fun b => C.U c ⊓ A.U a ⊓ B.U b) (fun _ => inf_le_left)
      (fun x hx => by
        obtain ⟨b, hb⟩ := exists_chart hB x
        exact Opens.mem_iSup.2 ⟨b, hx, hb⟩)
      (fun b => res (l₁ b) (v.s (c, b)) * res (l₂ b) (u.s (b, a))) (fun b b' x hx => by
        rw [val b x hx.1, val b' x hx.2, hu x (b, a) (b', a) (l₂ b hx.1) (l₂ b' hx.2),
          hv x (c, b) (c, b') (l₁ b hx.1) (l₁ b' hx.2), gm_self hA (𝟙 X) x hx.1.1.2, gm_self hC (𝟙 X) x hx.1.1.1,
          inv_one, mul_one, one_mul, mul_mul_mul_comm, inv_mul_cancel, one_mul])
    refine ⟨s, fun x b ha hb hc => ?_⟩
    have hx : x ∈ C.U c ⊓ A.U a ⊓ B.U b := ⟨⟨hc, ha⟩, hb⟩
    exact (gm_res (𝟙 X) x inf_le_left hx s).symm.trans ((congrArg (gm (𝟙 X) x _) (hs b)).trans (val b x hx))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, (isGen_iso_iff _).2 fun x p q hp hq => ?_, fun Y f y a b c ha hb hc =>
    gm_congr (fun x hx => hs c a x b hx.1.1.2 hx.2.1 hx.1.1.1) f y ⟨⟨⟨hc, ha⟩, hc, hb⟩, hb, ha⟩⟩
  obtain ⟨b, hb⟩ := exists_chart hB x
  refine (hs p.1 p.2 x b hp.2 hb hp.1).trans (Eq.trans ?_ (congrArg _ (hs q.1 q.2 x b hq.2 hb hq.1).symm))
  rw [hu x (b, p.2) (b, q.2) ⟨hb, hp.2⟩ ⟨hb, hq.2⟩, hv x (p.1, b) (q.1, b) ⟨hp.1, hb⟩ ⟨hq.1, hb⟩,
    gm_self hB (𝟙 X) x hb, inv_one, mul_one, one_mul, mul_mul_mul_comm]

end Iso

variable {X : ℕ → Scheme.{0}} (i : ∀ e, X e ⟶ X (e + 1))

structure FLB : Type 1 where

  ι : Type

  U : ∀ e, ι → (X e).Opens

  g : ∀ e a b, Γ(X e, U e a ⊓ U e b)ˣ
  isLB : ∀ e, LB.IsLB ⟨ι, U e, g e⟩
  U_eq : ∀ e a, U e a = i e ⁻¹ᵁ U (e + 1) a
  g_eq : ∀ e a b, g e a b = res (U := i e ⁻¹ᵁ (U (e + 1) a ⊓ U (e + 1) b))
    (le_inf (inf_le_left.trans (U_eq e a).le) (inf_le_right.trans (U_eq e b).le)) (pullU (i e) _ (g (e + 1) a b))

variable {i}

theorem eq_res_pullU_iff {Y Z : Scheme.{0}} (f : Z ⟶ Y) {U : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : Γ(Z, V)ˣ)
    (b : Γ(Y, U)ˣ) : a = res h (pullU f U b) ↔ ∀ z ∈ V, gm (𝟙 Z) z V a = gm f z U b := by
  have e : ∀ z ∈ V, gm (𝟙 Z) z V (res h (pullU f U b)) = gm f z U b := fun z hz =>
    (gm_res _ z h hz _).trans ((gm_pull (𝟙 Z) f z U (h hz) b).trans (by rw [Category.id_comp]))
  exact ⟨fun H z hz => H ▸ e z hz, fun H => unit_ext fun z hz => (H z hz).trans (e z hz).symm⟩

namespace FLB

abbrev lb (L : FLB i) (e : ℕ) : LB (X e) := ⟨L.ι, L.U e, L.g e⟩

theorem mem_succ (L : FLB i) {e : ℕ} {a : L.ι} {x : X e} (h : x ∈ L.U e a) : i e x ∈ L.U (e + 1) a := (L.U_eq e a).le h

theorem gm_g (L : FLB i) {e : ℕ} {a b : L.ι} {x : X e} (h : x ∈ L.U e a ⊓ L.U e b) :
    gm (𝟙 _) x _ (L.g e a b) = gm (i e) x _ (L.g (e + 1) a b) := (eq_res_pullU_iff _ _ _ _).1 (L.g_eq e a b) x h

theorem lb_iso_pull (L : FLB i) (e : ℕ) : LBIso (L.lb e) ((L.lb (e + 1)).pull (i e)) :=
  LBIso.chartPull (A := L.lb (e + 1)) (B := L.lb (e + 1)) (h := i e) ⟨fun a => a, fun a => (L.U_eq e a).le, fun _ _ _ ha hb => L.gm_g ⟨ha, hb⟩⟩
    (Geo.Tor.chartPullPull _ _ _ rfl) (PolBaseChange.lbIso_refl (L.isLB (e + 1)))

def Compat {L M : FLB i} (u : ∀ e, LB.Iso (L.lb e) (M.lb e)) : Prop :=
  ∀ e (p : M.ι × L.ι), (u e).s p = res (U := i e ⁻¹ᵁ (M.U (e + 1) p.1 ⊓ L.U (e + 1) p.2))
    (le_inf (inf_le_left.trans (M.U_eq e p.1).le) (inf_le_right.trans (L.U_eq e p.2).le)) (pullU (i e) _ ((u (e + 1)).s p))

theorem compat_iff {L M : FLB i} (u : ∀ e, LB.Iso (L.lb e) (M.lb e)) : Compat u ↔ ∀ e (p : M.ι × L.ι), ∀ x ∈ M.U e p.1 ⊓ L.U e p.2,
    gm (𝟙 _) x (M.U e p.1 ⊓ L.U e p.2) ((u e).s p) = gm (i e) x (M.U (e + 1) p.1 ⊓ L.U (e + 1) p.2) ((u (e + 1)).s p) :=
  forall₂_congr fun _ _ => eq_res_pullU_iff _ _ _ _

def Iso (L M : FLB i) : Prop := ∃ u : ∀ e, LB.Iso (L.lb e) (M.lb e), (∀ e, (u e).IsGen) ∧ Compat u

def reindex (L : FLB i) {κ : Type} (j : κ → L.ι) (h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k)) : FLB i where
  ι := κ
  U e k := L.U e (j k)
  g e k l := L.g e (j k) (j l)
  isLB e := ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 (h e x), fun _ => (L.isLB e).g_self _,
    fun _ _ _ => (L.isLB e).cocycle _ _ _⟩
  U_eq e k := L.U_eq e (j k)
  g_eq e k l := L.g_eq e (j k) (j l)

theorem reindex_iso (L : FLB i) {κ : Type} (j : κ → L.ι) (h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k)) :
    (L.reindex j h).Iso L := by
  refine ⟨fun e => ⟨fun p => L.g e p.1 (j p.2)⟩, fun e => (isGen_iso_iff _).2 fun x p q hp hq => ?_,
    fun e p => L.g_eq e p.1 (j p.2)⟩
  have a := gm_cocycle (L.isLB e) (𝟙 _) x hp.1 hq.1 hq.2
  have b := gm_cocycle (L.isLB e) (𝟙 _) x hp.1 hp.2 hq.2
  exact (eq_mul_inv_of_mul_eq (b.trans a.symm)).trans (mul_right_comm _ _ _)

theorem Iso.refl (L : FLB i) : L.Iso L := L.reindex_iso id fun e => exists_chart (L.isLB e)

theorem Iso.symm {L M : FLB i} (h : L.Iso M) : M.Iso L := by
  obtain ⟨u, hu, hc⟩ := h
  have le : ∀ e (p : L.ι × M.ι), L.U e p.1 ⊓ M.U e p.2 ≤ M.U e p.2 ⊓ L.U e p.1 := fun e p y hy => ⟨hy.2, hy.1⟩
  have v : ∀ e {Z : Scheme.{0}} (f : Z ⟶ X e) (z : Z) (p : L.ι × M.ι), f z ∈ L.U e p.1 ⊓ M.U e p.2 →
      gm f z (L.U e p.1 ⊓ M.U e p.2) (res (le e p) ((u e).s (p.2, p.1)))⁻¹ =
      (gm f z (M.U e p.2 ⊓ L.U e p.1) ((u e).s (p.2, p.1)))⁻¹ := fun e Z f z p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ z _ hp _))
  refine ⟨fun e => ⟨fun p => (res (le e p) ((u e).s (p.2, p.1)))⁻¹⟩, fun e => (isGen_iso_iff _).2 fun x p q hp hq => ?_,
    (compat_iff _).2 fun e p x hx => ?_⟩
  · refine (v e _ x p hp).trans (Eq.trans ?_ (congrArg _ (v e _ x q hq).symm))
    refine (congrArg (·⁻¹) ((isGen_iso_iff _).1 (hu e) x (p.2, p.1) (q.2, q.1) (le e p hp) (le e q hq))).trans ?_
    simp only [mul_inv, inv_inv]
    exact congrArg (· * _) (mul_comm _ _)
  · exact (v e _ x p hx).trans ((congrArg (·⁻¹) ((compat_iff u).1 hc e (p.2, p.1) x (le e p hx))).trans
      (v (e + 1) _ x p ⟨L.mem_succ hx.1, M.mem_succ hx.2⟩).symm)

theorem Iso.trans {L M N : FLB i} (h : L.Iso M) (h' : M.Iso N) : L.Iso N := by
  obtain ⟨u, hu, hc⟩ := h
  obtain ⟨v, hv, hd⟩ := h'
  choose w hw hg using fun e => exists_trans (L.isLB e) (M.isLB e) (N.isLB e) (hu e) (hv e)
  refine ⟨w, hw, (compat_iff _).2 fun e p x hx => ?_⟩
  obtain ⟨b, hb⟩ := exists_chart (M.isLB e) x
  exact (hg e _ (𝟙 _) x p.2 b p.1 hx.2 hb hx.1).trans ((congrArg₂ (· * ·)
    ((compat_iff v).1 hd e (p.1, b) x ⟨hx.1, hb⟩) ((compat_iff u).1 hc e (b, p.2) x ⟨hb, hx.2⟩)).trans
    (hg (e + 1) _ (i e) x p.2 b p.1 (L.mem_succ hx.2) (M.mem_succ hb) (N.mem_succ hx.1)).symm)

instance setoid : Setoid (FLB i) := ⟨Iso, Iso.refl, Iso.symm, Iso.trans⟩

variable {Y Y' : Scheme.{0}} (q : ∀ e, X e ⟶ Y) (hq : ∀ e, i e ≫ q (e + 1) = q e)

def ofPull (L : LB Y) (hL : L.IsLB) : FLB i :=
  have hU : ∀ e (a : PUnit → L.ι), (L.pull (q e)).U a = i e ⁻¹ᵁ (L.pull (q (e + 1))).U a := fun e a => by
    ext x
    refine mem_pull.trans (Iff.trans ?_ (mem_pull (F := q (e + 1)) (x := i e x)).symm)
    rw [← hq e]; rfl
  { ι := PUnit → L.ι
    U e := (L.pull (q e)).U
    g e := (L.pull (q e)).g
    isLB e := pull_isLB hL (q e)
    U_eq := hU
    g_eq e a b := (eq_res_pullU_iff _ _ _ _).2 fun x hx => by
      refine (gm_pull_g L (q e) (𝟙 _) x a b hx.1 hx.2).trans
        (Eq.trans ?_ (gm_pull_g L (q (e + 1)) (i e) x a b ((hU e a).le hx.1) ((hU e b).le hx.2)).symm)
      rw [Category.id_comp, hq] }

theorem ofPull_lb (L : LB Y) (hL : L.IsLB) (e : ℕ) : (ofPull q hq L hL).lb e = L.pull (q e) := rfl

theorem iso_of_chartPull {L M : FLB i} {A B : LB Y} (a : L.ι → A.ι) (b : M.ι → B.ι)
    (la : ∀ e k, L.U e k ≤ q e ⁻¹ᵁ A.U (a k)) (lb : ∀ e k, M.U e k ≤ q e ⁻¹ᵁ B.U (b k))
    (ga : ∀ e (x : X e) k l, x ∈ L.U e k → x ∈ L.U e l → gm (𝟙 _) x _ (L.g e k l) = gm (q e) x _ (A.g (a k) (a l)))
    (gb : ∀ e (x : X e) k l, x ∈ M.U e k → x ∈ M.U e l → gm (𝟙 _) x _ (M.g e k l) = gm (q e) x _ (B.g (b k) (b l)))
    (hq : ∀ e, i e ≫ q (e + 1) = q e) (h : LBIso A B) : L.Iso M := by
  obtain ⟨w, hw⟩ := h
  have le : ∀ e (p : M.ι × L.ι), M.U e p.1 ⊓ L.U e p.2 ≤ q e ⁻¹ᵁ (B.U (b p.1) ⊓ A.U (a p.2)) := fun e p y hy =>
    ⟨lb e _ hy.1, la e _ hy.2⟩
  have v : ∀ e {Z : Scheme.{0}} (f : Z ⟶ X e) (z : Z) (p : M.ι × L.ι), f z ∈ M.U e p.1 ⊓ L.U e p.2 →
      gm f z (M.U e p.1 ⊓ L.U e p.2) (res (le e p) (pullU (q e) _ (w.s (b p.1, a p.2)))) =
      gm (f ≫ q e) z (B.U (b p.1) ⊓ A.U (a p.2)) (w.s (b p.1, a p.2)) := fun e Z f z p hp =>
    (gm_res f z _ hp _).trans (gm_pull f (q e) z _ (le e p hp) _)
  refine ⟨fun e => ⟨fun p => res (le e p) (pullU (q e) _ (w.s (b p.1, a p.2)))⟩,
    fun e => (isGen_iso_iff _).2 fun x p r hp hr => ?_, (compat_iff _).2 fun e p x hx => ?_⟩
  · refine (v e _ x p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (fun s t => s * t⁻¹)
      (gb e x _ _ hp.1 hr.1) (ga e x _ _ hp.2 hr.2)) (v e _ x r hr)).symm)
    rw [Category.id_comp]
    have hm : q e x ∈ B.U (b p.1) ⊓ A.U (a p.2) ⊓ (B.U (b r.1) ⊓ A.U (a r.2)) := ⟨le e p hp, le e r hr⟩
    have := congrArg (gm (q e) x (B.U (b p.1) ⊓ A.U (a p.2) ⊓ (B.U (b r.1) ⊓ A.U (a r.2))))
      (hw (b p.1, a p.2) (b r.1, a r.2))
    exact (gm_res _ x _ hm _).symm.trans (this.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div A B (q e) x (b p.1, a p.2) (b r.1, a r.2) hm) (gm_res _ x _ hm _))))
  · refine (v e _ x p hx).trans (Eq.trans ?_ (v (e + 1) _ x p ⟨M.mem_succ hx.1, L.mem_succ hx.2⟩).symm)
    rw [Category.id_comp, hq]

theorem ofPull_iso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) : (ofPull q hq A hA).Iso (ofPull q hq B hB) :=
  iso_of_chartPull q (fun J => J ⟨⟩) (fun J => J ⟨⟩) (fun _ _ _ hx => mem_pull.1 hx) (fun _ _ _ hx => mem_pull.1 hx)
    (fun e x k l hk hl => (Geo.Tor.chartPullPull A (q e) (q e) rfl).g x k l hk hl)
    (fun e x k l hk hl => (Geo.Tor.chartPullPull B (q e) (q e) rfl).g x k l hk hl) hq h

theorem ofPull_comp (f : Y ⟶ Y') {A : LB Y'} (hA : A.IsLB) :
    (ofPull q hq (A.pull f) (pull_isLB hA f)).Iso
      (ofPull (fun e => q e ≫ f) (fun e => by rw [← Category.assoc, hq]) A hA) :=
  iso_of_chartPull (fun e => q e ≫ f) (fun J => J ⟨⟩ ⟨⟩) (fun J => J ⟨⟩) (fun e J x hx => (mem_pull (F := f) (x := q e x) (J := J ⟨⟩)).1 (mem_pull.1 hx))
    (fun _ _ _ hx => mem_pull.1 hx)
    (fun e x k l hk hl => ((Geo.Tor.chartPullPull (A.pull f) (q e) (q e) rfl).g x k l hk hl).trans
      (gm_pull_g A f (q e) x _ _ (mem_pull.1 hk) (mem_pull.1 hl)))
    (fun e x k l hk hl => (Geo.Tor.chartPullPull A (q e ≫ f) (q e ≫ f) rfl).g x k l hk hl)
    (fun e => by rw [← Category.assoc, hq]) (PolBaseChange.lbIso_refl hA)

end FLB

variable (i) in

structure FLBOn (κ : Type) : Type where

  U : ∀ e, κ → (X e).Opens

  g : ∀ e a b, Γ(X e, U e a ⊓ U e b)ˣ
  isLB : ∀ e, LB.IsLB ⟨κ, U e, g e⟩
  U_eq : ∀ e a, U e a = i e ⁻¹ᵁ U (e + 1) a
  g_eq : ∀ e a b, g e a b = res (U := i e ⁻¹ᵁ (U (e + 1) a ⊓ U (e + 1) b))
    (le_inf (inf_le_left.trans (U_eq e a).le) (inf_le_right.trans (U_eq e b).le)) (pullU (i e) _ (g (e + 1) a b))

def FLBOn.toFLB {κ : Type} (L : FLBOn i κ) : FLB i := ⟨κ, L.U, L.g, L.isLB, L.U_eq, L.g_eq⟩

def FLB.toOn (L : FLB i) : FLBOn i L.ι := ⟨L.U, L.g, L.isLB, L.U_eq, L.g_eq⟩

instance small_quotient : Small.{0} (Quotient (FLB.setoid (i := i))) := by
  refine small_of_surjective (α := FLBOn i (Σ e, X e)) (f := fun p => Quotient.mk _ p.toFLB) fun c => ?_
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  choose j hj using fun x : Σ e, X e => exists_chart (L.isLB x.1) x.2
  have h : ∀ e (x : X e), ∃ k, x ∈ L.U e (j k) := fun e x => ⟨⟨e, x⟩, hj ⟨e, x⟩⟩
  exact ⟨(L.reindex j h).toOn, Quotient.sound (L.reindex_iso j h)⟩

variable (i) in

def FPic : Type := Shrink.{0} (Quotient (FLB.setoid (i := i)))

def fcls (L : FLB i) : FPic i := equivShrink _ (Quotient.mk _ L)

theorem fcls_eq_iff {L M : FLB i} : fcls L = fcls M ↔ L.Iso M :=
  (equivShrink _).injective.eq_iff.trans (Quotient.eq (r := FLB.setoid))

theorem fcls_surj (c : FPic i) : ∃ L, fcls L = c := by
  obtain ⟨L, h⟩ := Quotient.exists_rep ((equivShrink _).symm c)
  exact ⟨L, (Equiv.eq_symm_apply _).1 h⟩

def level (e : ℕ) (c : FPic i) : SmallPic (X e) :=
  Quotient.lift (s := FLB.setoid) (fun L : FLB i => smallCls (L.lb e) (L.isLB e))
    (fun _ _ h => (smallCls_eq_iff _ _).2 (h.elim fun u hu => ⟨u e, hu.1 e⟩)) ((equivShrink _).symm c)

theorem level_fcls (e : ℕ) (L : FLB i) : level e (fcls L) = smallCls (L.lb e) (L.isLB e) := by
  rw [level, fcls, Equiv.symm_apply_apply]; rfl

theorem smallPull_level (e : ℕ) (c : FPic i) : smallPull (i e) (level (e + 1) c) = level e c := by
  obtain ⟨L, rfl⟩ := fcls_surj c
  rw [level_fcls, level_fcls, smallPull_smallCls _ _ (pull_isLB (L.isLB _) _)]
  exact (smallCls_eq_iff _ _).2 (L.lb_iso_pull e).symm

variable {Y Y' : Scheme.{0}} (q : ∀ e, X e ⟶ Y) (hq : ∀ e, i e ≫ q (e + 1) = q e)

def fpull (c : SmallPic Y) : FPic i :=
  Quotient.lift (s := CechPic.setoid Y) (fun A => fcls (FLB.ofPull q hq A.1 A.2))
    (fun A B h => fcls_eq_iff.2 (FLB.ofPull_iso q hq A.2 B.2 h)) (smallPicEquiv Y c)

theorem fpull_smallCls (L : LB Y) (hL : L.IsLB) : fpull q hq (smallCls L hL) = fcls (FLB.ofPull q hq L hL) := by
  rw [fpull, smallPicEquiv_smallCls]; rfl

theorem level_fpull (e : ℕ) (c : SmallPic Y) : level e (fpull q hq c) = smallPull (q e) c := by
  obtain ⟨L, hL, rfl⟩ := smallCls_surj c
  rw [fpull_smallCls, level_fcls, smallPull_smallCls _ _ (pull_isLB hL _)]
  rfl

theorem fpull_smallPull (f : Y ⟶ Y') (c : SmallPic Y') :
    fpull q hq (smallPull f c) = fpull (fun e => q e ≫ f) (fun e => by rw [← Category.assoc, hq]) c := by
  obtain ⟨L, hL, rfl⟩ := smallCls_surj c
  rw [smallPull_smallCls _ _ (pull_isLB hL _), fpull_smallCls, fpull_smallCls]
  exact fcls_eq_iff.2 (FLB.ofPull_comp q hq f hL)

theorem fpull_eq_iff (q' : ∀ e, X e ⟶ Y') (hq' : ∀ e, i e ≫ q' (e + 1) = q' e) {L : LB Y} (hL : L.IsLB) {M : LB Y'}
    (hM : M.IsLB) : fpull q hq (smallCls L hL) = fpull q' hq' (smallCls M hM) ↔
      ∃ u : ∀ e, LB.Iso (L.pull (q e)) (M.pull (q' e)), (∀ e, (u e).IsGen) ∧
        FLB.Compat (L := FLB.ofPull q hq L hL) (M := FLB.ofPull q' hq' M hM) u := by
  rw [fpull_smallCls, fpull_smallCls, fcls_eq_iff]; rfl

theorem fpull_id_injective (Y : Scheme.{0}) :
    Function.Injective (fpull (X := fun _ => Y) (i := fun _ => 𝟙 Y) (fun _ => 𝟙 Y) fun _ => Category.id_comp _) := by
  intro c d h
  have e := congrArg (level 0) h
  rw [level_fpull, level_fpull] at e
  simpa [smallPull, pull_id] using e

section Projective

open GlobalTheory.ProjSpace

variable {R : Type} [CommRing R] (I : Ideal R) (N : ℕ)

def projTrans (e : ℕ) : PSpace (R ⧸ I ^ (e + 1)) N ⟶ PSpace (R ⧸ I ^ (e + 1 + 1)) N :=
  baseChange N (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))

theorem projTrans_comp (e : ℕ) : projTrans I N e ≫ baseChange N (Ideal.Quotient.mk (I ^ (e + 1 + 1))) =
    baseChange N (Ideal.Quotient.mk (I ^ (e + 1))) := by
  rw [projTrans, ← baseChange_comp, Ideal.Quotient.factor_comp_mk]

def formalTwistingSheaf : FLB (X := fun e => PSpace (R ⧸ I ^ (e + 1)) N) (projTrans I N) :=
  FLB.ofPull (fun e => baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))) (projTrans_comp I N) (O1 R N) (O1_isLB R N)

theorem formalTwisting_ne_trivial (hI : I ≠ ⊤) : fcls (formalTwistingSheaf I (N + 1)) ≠
    fpull (X := fun e => PSpace (R ⧸ I ^ (e + 1)) (N + 1)) (fun e => baseChange (N + 1) (Ideal.Quotient.mk (I ^ (e + 1))))
      (projTrans_comp I (N + 1)) 0 := by
  intro h
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 (by simpa using hI)
  have e := congrArg (level 0) h
  rw [level_fpull, level_fcls, map_zero] at e
  have e' := ((smallCls_eq_iff _ (O1_isLB _ _)).2 (lbIso_pull_O1 (N + 1) (Ideal.Quotient.mk (I ^ (0 + 1))))).symm.trans e
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 ((smallPicEquiv _).symm.map_eq_zero_iff.1 e')
  exact Model.not_isGen_O1 t ht

end Projective

end GlobalTheory.FormalPic
