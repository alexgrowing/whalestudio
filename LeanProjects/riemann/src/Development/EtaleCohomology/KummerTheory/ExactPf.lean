import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ExactPf

open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (F.obj.map g.op ≫ φ.hom.app (op V)).hom x = (φ.hom.app (op U) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (a : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.res g x) = Sec.res (a ≫ g) x := by
  change _ = (F.obj.map (a ≫ g).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (s : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) s) = 0 := by
  change (Sec.map (I.d i j ≫ I.d j k) s) = 0
  rw [I.d_comp_d]
  rfl

theorem mneg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map φ (-x) = -Sec.map φ x :=
  map_neg _ _

theorem mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem rneg {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec.res g (-x) = -Sec.res g x :=
  map_neg _ _

theorem msub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _

theorem rsub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x - y) = Sec.res g x - Sec.res g y :=
  map_sub _ _ _

theorem rzero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem inj (F : Shv R) (m : ℤ) : Injective ((res R F).X m) := by
  unfold res; infer_instance

theorem tr (I : Cx R) {X : Scheme.{0}} (m k j : ℤ) (h : m = k) (a : Sec (I.X j) X) :
    (∃ b : Sec (I.X m) X, Sec.map (I.d m j) b = a) → ∃ b : Sec (I.X k) X, Sec.map (I.d k j) b = a := by
  subst h; exact id

theorem cls_eq (hD : Dict) (F : Shv R) {Y : Scheme.{0}} (m : ℤ) {x y : H R (sch.obj Y) F m}
    {s t : Sec ((res R F).X m) Y} (hx : IsCls x s) (hy : IsCls y t)
    (h : ∃ b : Sec ((res R F).X (m - 1)) Y, Sec.map ((res R F).d (m - 1) m) b = s - t) : x = y := by
  obtain ⟨-, -, D3, D4, -⟩ := hD R (res R F) Y m
  have h3 := (D4 x (-y) s (-t) hx (D4 y y t t hy hy).2).1
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h3
  exact sub_eq_zero.mp ((D3 _ _ h3).2.mpr h)

theorem Exact_of (hD : Dict) (hG : Glue) (hF : Flasque) : Exact := by
  intro R _ F W U V X a b f g hmv n
  have hpb := hmv.2.2.1
  haveI : IsOpenImmersion g := hmv.2.1
  haveI : Mono a := hpb.mono_fst_of_mono
  have hw : a ≫ f = b ≫ g := hpb.w
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
    obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
    have hau : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
    have hbv : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
    rw [huv] at hau
    have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
    have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
    obtain ⟨r, hr⟩ : ∃ r : Sec ((res R F).X (n - 1)) W,
        Sec.map ((res R F).d (n - 1) n) r = Sec.res a u0 - Sec.res b v0 := by
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hau ((hD R (res R F) W n).2.2.2.1 _ _ _ _ hbv hbv).2).1
      rw [add_neg_cancel, ← sub_eq_add_neg] at h3
      exact ((hD R (res R F) W n).2.2.1 _ _ h3).2.mp rfl
    haveI := inj F (n - 1)
    obtain ⟨r', hr'⟩ := hF R ((res R F).X (n - 1)) a r
    change Sec.res a r' = r at hr'
    have hu1 : Sec.res a (u0 - Sec.map ((res R F).d (n - 1) n) r') = Sec.res b v0 := by
      rw [rsub]
      rw [← map_res, hr', hr]
      abel
    obtain ⟨z, hzf, hzg⟩ := (hG R ((res R F).X n) a b f g hmv).2 _ v0 hu1
    have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := by
      apply (hG R ((res R F).X (n + 1)) a b f g hmv).1
      · rw [← map_res, hzf, msub, hu0c, dd, sub_zero]
      · rw [← map_res, hzg, hv0c]
    obtain ⟨x, hx⟩ := (hD R (res R F) X n).1 z hdz
    refine ⟨x, ?_, ?_⟩
    · have hfx : IsCls (pull R (sch.map f) F n x) (Sec.res f z) := (hD R (res R F) X n).2.2.2.2 f x z hx
      rw [hzf] at hfx
      refine cls_eq hD F n hfx hu0 ⟨-r', ?_⟩
      rw [mneg]
      abel
    · have hgx : IsCls (pull R (sch.map g) F n x) (Sec.res g z) := (hD R (res R F) X n).2.2.2.2 g x z hx
      rw [hzg] at hgx
      exact cls_eq hD F n hgx hv0 ⟨0, by rw [mzero, sub_self]⟩
  · intro x hfx hgx
    obtain ⟨z0, hz0⟩ := (hD R (res R F) X (n + 1)).2.1 x
    have hz0c := ((hD R (res R F) X (n + 1)).2.2.1 x z0 hz0).1
    have hgz : IsCls (pull R (sch.map g) F (n + 1) x) (Sec.res g z0) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 g x z0 hz0
    rw [hgx] at hgz
    obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) V (n + 1)).2.2.1 _ _ hgz).2.mp rfl)
    haveI := inj F n
    obtain ⟨t', ht'⟩ := hF R ((res R F).X n) g t
    change Sec.res g t' = t at ht'
    have hzg : Sec.res g (z0 - Sec.map ((res R F).d n (n + 1)) t') = 0 := by
      rw [rsub, ← map_res, ht', ht, sub_self]
    obtain ⟨x', hx'⟩ := (hD R (res R F) X (n + 1)).1 (z0 - Sec.map ((res R F).d n (n + 1)) t')
      (by rw [msub, hz0c, dd, sub_zero])
    have hxx : x' = x := cls_eq hD F (n + 1) hx' hz0
      (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t', by rw [mneg]; abel⟩)
    rw [hxx] at hx'
    have hfz : IsCls (pull R (sch.map f) F (n + 1) x) (Sec.res f (z0 - Sec.map ((res R F).d n (n + 1)) t')) :=
      (hD R (res R F) X (n + 1)).2.2.2.2 f x _ hx'
    rw [hfx] at hfz
    obtain ⟨s, hs⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
      (((hD R (res R F) U (n + 1)).2.2.1 _ _ hfz).2.mp rfl)
    have hsc : Sec.map ((res R F).d n (n + 1)) (Sec.res a s) = 0 := by
      rw [map_res, hs, res_res, hw, ← res_res, hzg, rzero]
    obtain ⟨w, hw'⟩ := (hD R (res R F) W n).1 _ hsc
    exact ⟨w, s, _, hw', hx', hs.symm, hzg⟩
  · intro w
    constructor
    · rintro ⟨s, z, hws, hz0, hfz, hgz⟩
      obtain ⟨t, ht⟩ := tr (res R F) (n + 1 - 1) n (n + 1) (by ring) _
        (((hD R (res R F) X (n + 1)).2.2.1 _ _ hz0).2.mp rfl)
      have hu : Sec.map ((res R F).d n (n + 1)) (s - Sec.res f t) = 0 := by
        rw [msub, map_res, ht, hfz, sub_self]
      have hv : Sec.map ((res R F).d n (n + 1)) (-Sec.res g t) = 0 := by
        rw [mneg, map_res, ht, hgz, neg_zero]
      obtain ⟨u, hu'⟩ := (hD R (res R F) U n).1 _ hu
      obtain ⟨v, hv'⟩ := (hD R (res R F) V n).1 _ hv
      refine ⟨u, v, ?_⟩
      have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a (s - Sec.res f t)) :=
        (hD R (res R F) U n).2.2.2.2 a u _ hu'
      have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b (-Sec.res g t)) :=
        (hD R (res R F) V n).2.2.2.2 b v _ hv'
      have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
      have hA : Sec.res a (s - Sec.res f t) + -Sec.res b (-Sec.res g t) = Sec.res a s := by
        rw [rsub, rneg, res_res, res_res, hw]
        abel
      rw [hA, ← sub_eq_add_neg] at h3
      exact cls_eq hD F n hws h3 ⟨0, by rw [mzero, sub_self]⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u0, hu0⟩ := (hD R (res R F) U n).2.1 u
      obtain ⟨v0, hv0⟩ := (hD R (res R F) V n).2.1 v
      have hu0c := ((hD R (res R F) U n).2.2.1 u u0 hu0).1
      have hv0c := ((hD R (res R F) V n).2.2.1 v v0 hv0).1
      haveI := inj F n
      obtain ⟨s', hs'⟩ := hF R ((res R F).X n) a (Sec.res b v0)
      change Sec.res a s' = Sec.res b v0 at hs'
      obtain ⟨t, htf, htg⟩ := (hG R ((res R F).X n) a b f g hmv).2 s' v0 hs'
      refine ⟨u0 - s', -Sec.map ((res R F).d n (n + 1)) t, ?_, ?_, ?_, ?_⟩
      · have h1 : IsCls (pull R (sch.map a) F n u) (Sec.res a u0) := (hD R (res R F) U n).2.2.2.2 a u u0 hu0
        have h2 : IsCls (pull R (sch.map b) F n v) (Sec.res b v0) := (hD R (res R F) V n).2.2.2.2 b v v0 hv0
        have h3 := ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h1 ((hD R (res R F) W n).2.2.2.1 _ _ _ _ h2 h2).2).1
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← hs', ← rsub] at h3
        exact h3
      · obtain ⟨y, hy⟩ := (hD R (res R F) X (n + 1)).1 (-Sec.map ((res R F).d n (n + 1)) t)
          (by rw [mneg, dd, neg_zero])
        have hy0 : y = 0 := ((hD R (res R F) X (n + 1)).2.2.1 _ _ hy).2.mpr
          (tr (res R F) n (n + 1 - 1) (n + 1) (by ring) _ ⟨-t, mneg _ _⟩)
        rw [hy0] at hy
        exact hy
      · rw [rneg, ← map_res, htf, msub, hu0c, zero_sub]
      · rw [rneg, ← map_res, htg, hv0c, neg_zero]

end LateralTheory.KummerTheory.ExactPf
