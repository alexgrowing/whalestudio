import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Development.EtaleCohomology.KummerTheory.FlasquePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.DictPf

abbrev Qp {X : Scheme.{0}} (U : X.Opens) : PSh := pushout (yoneda.map U.ι) (yoneda.map U.ι)

abbrev Qmap {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) : Qp U' ⟶ Qp U :=
  pushout.map _ _ _ _ (yoneda.map f) (yoneda.map f) (yoneda.map (f.resLE U U' h))
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])

def ev {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G) : Sec G X :=
  (m.hom.app (op X)).hom (freeGen R (yoneda.obj X) X (𝟙 X))

def LeafEv : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}),
  Function.Injective (ev (R := R) (G := G) (X := X)) ∧
  (∀ m m' : (free R).obj (yoneda.obj X) ⟶ G, ev (m + m') = ev m + ev m') ∧
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (m : (free R).obj (yoneda.obj X) ⟶ G),
    ev ((free R).map (yoneda.map f) ≫ m) = Sec.res f (ev m)

def LeafPair : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (U : X.Opens),
  (∀ s s' : Sec G X, Sec.res U.ι s = Sec.res U.ι s' → ∃ m : (free R).obj (Qp U) ⟶ G,
    ev ((free R).map (pushout.inl _ _) ≫ m) = s ∧ ev ((free R).map (pushout.inr _ _) ≫ m) = s') ∧
  ∀ m m' : (free R).obj (Qp U) ⟶ G, (free R).map (pushout.inl _ _) ≫ m = (free R).map (pushout.inl _ _) ≫ m' →
    (free R).map (pushout.inr _ _) ≫ m = (free R).map (pushout.inr _ _) ≫ m' → m = m'

def LeafDbl : Prop := ∃ e : ∀ {X : Scheme.{0}} (U : X.Opens), disc.obj (Qp U) ≅ dbl (opn U),
  (∀ {X : Scheme.{0}} (U : X.Opens), disc.map (pushout.inl _ _) ≫ (e U).hom = dbl.inl (opn U)) ∧
  (∀ {X : Scheme.{0}} (U : X.Opens), disc.map (pushout.inr _ _) ≫ (e U).hom = dbl.inr (opn U)) ∧
  ∀ {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U),
    disc.map (Qmap f U' U h) ≫ (e U).hom = (e U').hom ≫ dbl.map (opnMap f U' U h)

theorem ev_comp {R : Type} [CommRing R] {G G' : Shv R} {X : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G)
    (g : G ⟶ G') : ev (m ≫ g) = Sec.map g (ev m) := rfl

section
variable {R : Type} [CommRing R] (hE : LeafEv) (hP : LeafPair)
include hE

theorem ev_zero {G : Shv R} {X : Scheme.{0}} : ev (0 : (free R).obj (yoneda.obj X) ⟶ G) = 0 := by
  have h := (hE R G X).2.1 0 0
  rw [add_zero] at h
  simpa using h

theorem eq_zero_of_ev {G : Shv R} {X : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G) (h : ev m = 0) : m = 0 :=
  (hE R G X).1 (h.trans (ev_zero hE).symm)

include hP

theorem ext_ev {G : Shv R} {X : Scheme.{0}} {U : X.Opens} (m m' : (free R).obj (Qp U) ⟶ G)
    (h1 : ev ((free R).map (pushout.inl _ _) ≫ m) = ev ((free R).map (pushout.inl _ _) ≫ m'))
    (h2 : ev ((free R).map (pushout.inr _ _) ≫ m) = ev ((free R).map (pushout.inr _ _) ≫ m')) : m = m' :=
  (hP R G X U).2 m m' ((hE R G X).1 h1) ((hE R G X).1 h2)

end

theorem res_pair {R : Type} [CommRing R] (hE : LeafEv) {G : Shv R} {X : Scheme.{0}} {U : X.Opens}
    (m : (free R).obj (Qp U) ⟶ G) :
    Sec.res U.ι (ev ((free R).map (pushout.inl _ _) ≫ m)) = Sec.res U.ι (ev ((free R).map (pushout.inr _ _) ≫ m)) := by
  rw [← (hE R G X).2.2, ← (hE R G X).2.2, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    pushout.condition]

theorem sres_zero {R : Type} [CommRing R] {G : Shv R} {X Y : Scheme.{0}} (f : Y ⟶ X) : Sec.res f (0 : Sec G X) = 0 :=
  map_zero (G.obj.map f.op).hom

theorem sres_sub {R : Type} [CommRing R] {G : Shv R} {X Y : Scheme.{0}} (f : Y ⟶ X) (a b : Sec G X) :
    Sec.res f (a - b) = Sec.res f a - Sec.res f b := map_sub (G.obj.map f.op).hom a b

theorem smap_sub {R : Type} [CommRing R] {G G' : Shv R} (g : G ⟶ G') {X : Scheme.{0}} (a b : Sec G X) :
    Sec.map g (a - b) = Sec.map g a - Sec.map g b := map_sub (g.hom.app (op X)).hom a b

theorem smap_zero {R : Type} [CommRing R] {G G' : Shv R} (g : G ⟶ G') {X : Scheme.{0}} :
    Sec.map g (0 : Sec G X) = 0 := map_zero (g.hom.app (op X)).hom

def mk (hP : LeafPair) {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (U : X.Opens) (s s' : Sec G X)
    (h : Sec.res U.ι s = Sec.res U.ι s') : (free R).obj (Qp U) ⟶ G := ((hP R G X U).1 s s' h).choose

theorem mk_l (hP : LeafPair) {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (U : X.Opens) (s s' : Sec G X)
    (h : Sec.res U.ι s = Sec.res U.ι s') : ev ((free R).map (pushout.inl _ _) ≫ mk hP U s s' h) = s :=
  ((hP R G X U).1 s s' h).choose_spec.1

theorem mk_r (hP : LeafPair) {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (U : X.Opens) (s s' : Sec G X)
    (h : Sec.res U.ι s = Sec.res U.ι s') : ev ((free R).map (pushout.inr _ _) ≫ mk hP U s s' h) = s' :=
  ((hP R G X U).1 s s' h).choose_spec.2

abbrev KK (q : ℕ) (i : ℤ) : Cx (ZMod q) := res (ZMod q) (tw q i)

section
variable (hD : Cl.LeafDisc) (hE : LeafEv) (hP : LeafPair) (hB : LeafDbl) (q : ℕ) (n i : ℤ)

def clD := (hD (ZMod q) (KK q i) n).choose

theorem clD_add (P : PSh) (a b : (free (ZMod q)).obj P ⟶ (KK q i).X n) (ha : a ≫ (KK q i).d n (n + 1) = 0)
    (hb : b ≫ (KK q i).d n (n + 1) = 0) : clD hD q n i P (a + b) = clD hD q n i P a + clD hD q n i P b :=
  (hD (ZMod q) (KK q i) n).choose_spec.1 P a b ha hb

theorem clD_surj (P : PSh) (x : CohomologyClass ((chains (ZMod q)).obj (disc.obj P)) (KK q i) n) :
    ∃ a, a ≫ (KK q i).d n (n + 1) = 0 ∧ clD hD q n i P a = x :=
  (hD (ZMod q) (KK q i) n).choose_spec.2.1 P x

theorem clD_ker (P : PSh) (a : (free (ZMod q)).obj P ⟶ (KK q i).X n) (ha : a ≫ (KK q i).d n (n + 1) = 0) :
    clD hD q n i P a = 0 ↔ ∃ b, b ≫ (KK q i).d (n - 1) n = a :=
  (hD (ZMod q) (KK q i) n).choose_spec.2.2.1 P a ha

def eD : ∀ {X : Scheme.{0}} (U : X.Opens), disc.obj (Qp U) ≅ dbl (opn U) := hB.choose

theorem eD_r {X : Scheme.{0}} (U : X.Opens) : disc.map (pushout.inr _ _) ≫ (eD hB U).hom = dbl.inr (opn U) :=
  hB.choose_spec.2.1 U

theorem eD_n {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) :
    disc.map (Qmap f U' U h) ≫ (eD hB U).hom = (eD hB U').hom ≫ dbl.map (opnMap f U' U h) :=
  hB.choose_spec.2.2 f U' U h

theorem zc_res {X : Scheme.{0}} {U : X.Opens} (a : Cl.Zc (KK q i) U n) : Sec.res U.ι a.1 = Sec.res U.ι 0 := by
  rw [((Cl.mem_Zc _).1 a.2).1, sres_zero]

def Mz {X : Scheme.{0}} (U : X.Opens) (a : Cl.Zc (KK q i) U n) : (free (ZMod q)).obj (Qp U) ⟶ (KK q i).X n :=
  mk hP U a.1 0 (zc_res q n i a)

theorem cl_zero (P : PSh) : clD hD q n i P 0 = 0 := by
  have h := clD_add hD q n i P 0 0 zero_comp zero_comp
  rw [add_zero] at h
  simpa using h

include hE hP in
theorem coc {X : Scheme.{0}} {U : X.Opens} {k : ℤ} (m : (free (ZMod q)).obj (Qp U) ⟶ (KK q i).X k)
    (h1 : Sec.map ((KK q i).d k (k + 1)) (ev ((free _).map (pushout.inl _ _) ≫ m)) = 0)
    (h2 : Sec.map ((KK q i).d k (k + 1)) (ev ((free _).map (pushout.inr _ _) ≫ m)) = 0) :
    m ≫ (KK q i).d k (k + 1) = 0 := by
  apply ext_ev hE hP
  · rw [comp_zero, ev_zero hE, ← Category.assoc, ev_comp, h1]
  · rw [comp_zero, ev_zero hE, ← Category.assoc, ev_comp, h2]

include hE in
theorem Mz_coc {X : Scheme.{0}} {U : X.Opens} (a : Cl.Zc (KK q i) U n) : Mz hP q n i U a ≫ (KK q i).d n (n + 1) = 0 :=
  coc hE hP q i _ (by unfold Mz; rw [mk_l]; exact ((Cl.mem_Zc _).1 a.2).2) (by unfold Mz; rw [mk_r, smap_zero])

theorem pull_cl (P' P : PSh) (f : P' ⟶ P) (m : (free (ZMod q)).obj P ⟶ (KK q i).X n) (hm : m ≫ (KK q i).d n (n + 1) = 0) :
    pull _ (disc.map f) (tw q i) n (clD hD q n i P m) = clD hD q n i P' ((free _).map f ≫ m) :=
  (hD (ZMod q) (KK q i) n).choose_spec.2.2.2 P' P f m hm

def clsV {X : Scheme.{0}} (U : X.Opens) (a : Cl.Zc (KK q i) U n) : Ht q (dbl (opn U)) n i :=
  pull _ (eD hB U).inv (tw q i) n (clD hD q n i (Qp U) (Mz hP q n i U a))

theorem inr_inv {X : Scheme.{0}} (U : X.Opens) : dbl.inr (opn U) ≫ (eD hB U).inv = disc.map (pushout.inr _ _) := by
  exact (Iso.comp_inv_eq _).2 (eD_r hB U).symm

include hE in
theorem clsV_mem {X : Scheme.{0}} (U : X.Opens) (a : Cl.Zc (KK q i) U n) : clsV hD hP hB q n i U a ∈ Hs q (opn U) n i := by
  change pull _ (dbl.inr (opn U)) (tw q i) n (pull _ (eD hB U).inv (tw q i) n _) = 0
  rw [← pull_comp, inr_inv]
  erw [pull_cl hD q n i (yoneda.obj X) (Qp U) (pushout.inr _ _) _ (Mz_coc hE hP q n i a)]
  have : (free (ZMod q)).map (pushout.inr _ _) ≫ Mz hP q n i U a = 0 := by
    apply eq_zero_of_ev hE
    unfold Mz; rw [mk_r]
  rw [this, cl_zero]
  rfl

include hE in
theorem Mz_add {X : Scheme.{0}} {U : X.Opens} (a b : Cl.Zc (KK q i) U n) :
    Mz hP q n i U (a + b) = Mz hP q n i U a + Mz hP q n i U b := by
  apply ext_ev hE hP
  · rw [Preadditive.comp_add, (hE _ _ _).2.1]; unfold Mz; rw [mk_l, mk_l, mk_l]; try rfl
  · rw [Preadditive.comp_add, (hE _ _ _).2.1]; unfold Mz; rw [mk_r, mk_r, mk_r, add_zero]

theorem pinv_eq_zero {X : Scheme.{0}} (U : X.Opens) (c : H (ZMod q) (disc.obj (Qp U)) (tw q i) n) :
    pull _ (eD hB U).inv (tw q i) n c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h2 := congrArg (pull _ (eD hB U).hom (tw q i) n) h
    rwa [← pull_comp, Iso.hom_inv_id, pull_id, map_zero] at h2
  · intro h; rw [h, map_zero]

include hD hE hP hB

def cls {X : Scheme.{0}} (U : X.Opens) : Cl.Zc (KK q i) U n →+ Hs q (opn U) n i :=
  AddMonoidHom.mk' (fun a => ⟨clsV hD hP hB q n i U a, clsV_mem hD hE hP hB q n i U a⟩) (fun a b => by
    apply Subtype.ext
    show clsV hD hP hB q n i U (a + b) = clsV hD hP hB q n i U a + clsV hD hP hB q n i U b
    unfold clsV
    rw [Mz_add hE hP q n i a b, clD_add hD q n i _ _ _ (Mz_coc hE hP q n i a) (Mz_coc hE hP q n i b), map_add])

theorem cls_surj {X : Scheme.{0}} (U : X.Opens) : Function.Surjective (cls hD hE hP hB q n i U) := by
  intro x
  obtain ⟨m, hm, hmx⟩ := clD_surj hD q n i (Qp U) (pull _ (eD hB U).hom (tw q i) n x.1)
  have h0 : clD hD q n i (yoneda.obj X) ((free _).map (pushout.inr _ _) ≫ m) = 0 := by
    erw [← pull_cl hD q n i (yoneda.obj X) (Qp U) (pushout.inr _ _) m hm]
    rw [hmx, ← pull_comp, eD_r]
    exact x.2
  have hc' : ((free _).map (pushout.inr _ _) ≫ m) ≫ (KK q i).d n (n + 1) = 0 := by
    rw [Category.assoc, hm, comp_zero]
  obtain ⟨b, hb⟩ := (clD_ker hD q n i _ _ hc').1 h0
  have ht : Sec.map ((KK q i).d (n - 1) n) (ev b) = ev ((free _).map (pushout.inr _ _) ≫ m) := by
    rw [← ev_comp, hb]
  have mem : ev ((free _).map (pushout.inl _ _) ≫ m) - ev ((free _).map (pushout.inr _ _) ≫ m) ∈ Cl.Zc (KK q i) U n := by
    refine (Cl.mem_Zc _).2 ⟨by rw [sres_sub, res_pair hE m, sub_self], ?_⟩
    simp only [smap_sub, ← ev_comp, Category.assoc, hm, comp_zero, ev_zero hE, sub_zero]
  let a : Cl.Zc (KK q i) U n := ⟨_, mem⟩
  let N := mk hP U (ev b) (ev b) rfl
  have N_l : ev ((free _).map (pushout.inl _ _) ≫ N) = ev b := mk_l hP U (ev b) (ev b) rfl
  have N_r : ev ((free _).map (pushout.inr _ _) ≫ N) = ev b := mk_r hP U (ev b) (ev b) rfl
  have hM : m = Mz hP q n i U a + N ≫ (KK q i).d (n - 1) n := by
    apply ext_ev hE hP
    · rw [Preadditive.comp_add, (hE _ _ _).2.1, ← Category.assoc ((free _).map (pushout.inl _ _)) N,
        ev_comp ((free _).map (pushout.inl _ _) ≫ N), N_l, ht]
      unfold Mz; rw [mk_l]; exact (sub_add_cancel _ _).symm
    · rw [Preadditive.comp_add, (hE _ _ _).2.1, ← Category.assoc ((free _).map (pushout.inr _ _)) N,
        ev_comp ((free _).map (pushout.inr _ _) ≫ N), N_r, ht]
      unfold Mz; rw [mk_r, zero_add]
  have hNc : (N ≫ (KK q i).d (n - 1) n) ≫ (KK q i).d n (n + 1) = 0 := by
    rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  have hN : clD hD q n i (Qp U) (N ≫ (KK q i).d (n - 1) n) = 0 := (clD_ker hD q n i _ _ hNc).2 ⟨N, rfl⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  show clsV hD hP hB q n i U a = x.1
  unfold clsV
  have key : clD hD q n i (Qp U) (Mz hP q n i U a) = pull _ (eD hB U).hom (tw q i) n x.1 := by
    calc clD hD q n i (Qp U) (Mz hP q n i U a)
        = clD hD q n i (Qp U) (Mz hP q n i U a + N ≫ (KK q i).d (n - 1) n) := by
          rw [clD_add hD q n i _ _ _ (Mz_coc hE hP q n i a) hNc, hN, add_zero]
      _ = clD hD q n i (Qp U) m := by rw [← hM]
      _ = _ := hmx
  rw [key, ← pull_comp, Iso.inv_hom_id, pull_id]

theorem cls_ker {X : Scheme.{0}} (U : X.Opens) (a : Cl.Zc (KK q i) U n) :
    cls hD hE hP hB q n i U a = 0 ↔ Cl.Bd (KK q i) U n a.1 := by
  rw [Subtype.ext_iff]
  change clsV hD hP hB q n i U a = 0 ↔ _
  unfold clsV
  rw [pinv_eq_zero hB q n i U, clD_ker hD q n i _ _ (Mz_coc hE hP q n i a)]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨ev ((free _).map (pushout.inl _ _) ≫ b) - ev ((free _).map (pushout.inr _ _) ≫ b),
      by rw [sres_sub, res_pair hE b, sub_self], ?_⟩
    rw [smap_sub, ← ev_comp, ← ev_comp, Category.assoc, Category.assoc, hb]
    unfold Mz; rw [mk_l, mk_r, sub_zero]
  · rintro ⟨c, hc0, hc⟩
    refine ⟨mk hP U c 0 (by rw [hc0, sres_zero]), ?_⟩
    apply ext_ev hE hP
    · rw [← Category.assoc, ev_comp, mk_l, hc]; unfold Mz; rw [mk_l]
    · rw [← Category.assoc, ev_comp, mk_r, smap_zero]; unfold Mz; rw [mk_r]

theorem cls_nat {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U)
    (a : Cl.Zc (KK q i) U n) (a' : Cl.Zc (KK q i) U' n) (ha : a'.1 = Sec.res f a.1) :
    Hs.pull q (opnMap f U' U h) n i (cls hD hE hP hB q n i U a) = cls hD hE hP hB q n i U' a' := by
  apply Subtype.ext
  show pull _ (dbl.map (opnMap f U' U h)) (tw q i) n (clsV hD hP hB q n i U a) = clsV hD hP hB q n i U' a'
  unfold clsV
  rw [← pull_comp]
  have e1 : dbl.map (opnMap f U' U h) ≫ (eD hB U).inv = (eD hB U').inv ≫ disc.map (Qmap f U' U h) := by
    rw [Iso.comp_inv_eq, Category.assoc, eD_n, Iso.inv_hom_id_assoc]
  rw [e1, pull_comp]
  erw [pull_cl hD q n i _ _ (Qmap f U' U h) _ (Mz_coc hE hP q n i a)]
  have il : pushout.inl _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inl _ _ := pushout.inl_desc _ _ _
  have ir : pushout.inr _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inr _ _ := pushout.inr_desc _ _ _
  have hm : (free _).map (Qmap f U' U h) ≫ Mz hP q n i U a = Mz hP q n i U' a' := by
    apply ext_ev hE hP
    · rw [← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, (hE _ _ _).2.2]
      unfold Mz; rw [mk_l, mk_l, ha]
    · rw [← Category.assoc, ← Functor.map_comp, ir, Functor.map_comp, Category.assoc, (hE _ _ _).2.2]
      unfold Mz; rw [mk_r, mk_r, sres_zero]
  rw [hm]

end

theorem LeafDict_of (hD : Cl.LeafDisc) (hE : LeafEv) (hP : LeafPair) (hB : LeafDbl) : Cl.LeafDict := fun q n i =>
  ⟨fun U => cls hD hE hP hB q n i U, fun U => cls_surj hD hE hP hB q n i U, fun U a => cls_ker hD hE hP hB q n i U a,
    fun f U' U h a a' ha => cls_nat hD hE hP hB q n i f U' U h a a' ha⟩

end LateralTheory.CohomologicalPurity.DictPf
