import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DeltaPf
open LateralTheory.KummerTheory LateralTheory.KummerTheory.ContCut

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (a : V ⟶ U) (x : Sec F U) :
    Sec.res a (Sec.map φ x) = Sec.map φ (Sec.res a x) :=
  (congrArg (fun h => h.hom x) (φ.hom.naturality a.op)).symm

theorem sec_map_comp {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem res_add {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x y : Sec F U) :
    Sec.res a (x + y) = Sec.res a x + Sec.res a y := map_add _ _ _
theorem res_sub {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x y : Sec F U) :
    Sec.res a (x - y) = Sec.res a x - Sec.res a y := map_sub _ _ _
theorem res_neg {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) (x : Sec F U) :
    Sec.res a (-x) = -Sec.res a x := map_neg _ _
theorem res_zero {F : Shv R} {V U : Scheme.{0}} (a : V ⟶ U) : Sec.res a (0 : Sec F U) = 0 := map_zero _
theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (-x) = -Sec.map φ x := map_neg _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (x : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) x) = 0 := by
  rw [← sec_map_comp, I.d_comp_d, sec_map_zero]

instance injRes (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

theorem mono_a {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
    (h : IsMV a b f g) : Mono a := by
  obtain ⟨_, hg, hp, _⟩ := h
  haveI := hg
  refine ⟨fun x y e => hp.hom_ext e ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← hp.w, reassoc_of% e]

variable {F : Shv R} {W U V X : Scheme.{0}} {a : W ⟶ U} {b : W ⟶ V} {f : U ⟶ X} {g : V ⟶ X} {n : ℤ}

theorem conn_total (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g)
    (w : H R (sch.obj W) F n) : ∃ x, Conn F a f g n w x := by
  haveI := mono_a h
  obtain ⟨c, hc⟩ := (hD R (res R F) W n).2.1 w
  obtain ⟨s, rfl⟩ := hF R ((res R F).X n) a c
  have hcl := ((hD R (res R F) W n).2.2.1 w _ hc).1
  obtain ⟨-, hglue⟩ := hG R ((res R F).X (n + 1)) a b f g h
  obtain ⟨z, hz1, hz2⟩ := hglue (Sec.map ((res R F).d n (n + 1)) s) 0
    (by rw [sec_res_map, hcl, res_zero])
  have hzc : Sec.map ((res R F).d (n + 1) (n + 1 + 1)) z = 0 := by
    apply (hG R ((res R F).X (n + 1 + 1)) a b f g h).1
    · rw [sec_res_map, hz1, dd]
    · rw [sec_res_map, hz2, smap_zero]
  obtain ⟨x, hx⟩ := (hD R (res R F) X (n + 1)).1 z hzc
  exact ⟨x, s, z, hc, hx, hz1, hz2⟩

theorem conn_add (hD : Dict) {w w' x x'} (h1 : Conn F a f g n w x) (h2 : Conn F a f g n w' x') :
    Conn F a f g n (w + w') (x + x') := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h1
  obtain ⟨s', z', hs', hz', e1', e2'⟩ := h2
  refine ⟨s + s', z + z', ?_, ((hD R _ X (n + 1)).2.2.2.1 _ _ _ _ hz hz').1, ?_, ?_⟩
  · rw [res_add]; exact ((hD R _ W n).2.2.2.1 _ _ _ _ hs hs').1
  · rw [res_add, smap_add, e1, e1']
  · rw [res_add, e2, e2', add_zero]

theorem conn_neg (hD : Dict) {w x} (h1 : Conn F a f g n w x) : Conn F a f g n (-w) (-x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h1
  refine ⟨-s, -z, ?_, ((hD R _ X (n + 1)).2.2.2.1 _ _ _ _ hz hz).2, ?_, ?_⟩
  · rw [res_neg]; exact ((hD R _ W n).2.2.2.1 _ _ _ _ hs hs).2
  · rw [res_neg, smap_neg, e1]
  · rw [res_neg, e2, neg_zero]

theorem conn_zero (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g) {x}
    (hx : Conn F a f g n 0 x) : x = 0 := by
  haveI := mono_a h
  obtain ⟨s, z, hs, hz, e1, e2⟩ := hx
  obtain ⟨c, hc⟩ := ((hD R (res R F) W n).2.2.1 0 _ hs).2.mp rfl
  obtain ⟨s', rfl⟩ := hF R ((res R F).X (n - 1)) a c
  beta_reduce at hc
  obtain ⟨-, hglue⟩ := hG R ((res R F).X n) a b f g h
  obtain ⟨t, ht1, ht2⟩ := hglue (s - Sec.map ((res R F).d (n - 1) n) s') 0
    (by rw [res_sub, sec_res_map, hc, sub_self, res_zero])
  have hzt : Sec.map ((res R F).d n (n + 1)) t = z := by
    refine sub_eq_zero.1 ((hG R ((res R F).X (n + 1)) a b f g h).1 _ ?_ ?_)
    · rw [res_sub, sec_res_map, ht1, e1, smap_sub, dd, sub_zero, sub_self]
    · rw [res_sub, sec_res_map, ht2, e2, smap_zero, sub_self]
  refine ((hD R (res R F) X (n + 1)).2.2.1 x z hz).2.mpr
    ⟨Sec.map ((res R F).XIsoOfEq (by ring : n = n + 1 - 1)).hom t, ?_⟩
  rw [← sec_map_comp, HomologicalComplex.XIsoOfEq_hom_comp_d, hzt]

theorem conn_unique (hD : Dict) (hG : Glue) (hF : Flasque) (h : IsMV a b f g) {w x x'}
    (h1 : Conn F a f g n w x) (h2 : Conn F a f g n w x') : x = x' := by
  have h3 := conn_add hD h1 (conn_neg hD h2)
  rw [add_neg_cancel] at h3
  have := conn_zero hD hG hF h h3
  rwa [← sub_eq_add_neg, sub_eq_zero] at this

end LateralTheory.KummerTheory.DeltaPf

namespace LateralTheory.KummerTheory.ContCut
open LateralTheory.KummerTheory.DeltaPf

theorem Delta_of (hD : Dict) (hG : Glue) (hF : Flasque) : Delta := by
  intro R _ F W U V X a b f g h n
  have tot := fun w => conn_total (F := F) (n := n) hD hG hF h w
  refine ⟨AddMonoidHom.mk' (fun w => Classical.choose (tot w)) (fun w w' =>
    conn_unique hD hG hF h (Classical.choose_spec (tot (w + w')))
      (conn_add hD (Classical.choose_spec (tot w)) (Classical.choose_spec (tot w')))), fun w x => ⟨fun hx =>
    conn_unique hD hG hF h (Classical.choose_spec (tot w)) hx, fun e => e ▸ Classical.choose_spec (tot w)⟩⟩

end LateralTheory.KummerTheory.ContCut
