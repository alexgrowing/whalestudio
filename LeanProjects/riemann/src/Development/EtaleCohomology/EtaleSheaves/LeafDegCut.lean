import Development.EtaleCohomology.EtaleSheaves.LeafRepCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafDegCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def Cov {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop) : Prop :=
  ∃ S ∈ (EtTop B) U, ∀ (U' : B.Etale) (a : U' ⟶ U), S a → P U' a

theorem Cov.mono {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Q U' a) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun U' a ha => hPQ U' a (hP U' a ha)⟩

theorem Cov.and {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P) (h' : Cov U Q) :
    Cov U (fun U' a => P U' a ∧ Q U' a) := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hQ⟩ := h'
  exact ⟨S ⊓ S', (EtTop B).intersection_covering hS hS', fun U' a ha => ⟨hP U' a ha.1, hQ U' a ha.2⟩⟩

theorem Cov.all {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : ∀ U' a, P U' a) : Cov U P :=
  ⟨⊤, (EtTop B).top_mem U, fun U' a _ => h U' a⟩

def SHV (q : ℕ) (i : ℤ) {B Y0 Y1 Y2 : Scheme.{0}} (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) : Prop :=
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)

abbrev rY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm m

abbrev rB (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm m

abbrev gY (q : ℕ) (i : ℤ) {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm m

abbrev bY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm m

def LeafNeg : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ), m < 0 →
  Subsingleton (Hrel R f F m)

def LeafShMapZero : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q)) (f : K ⟶ K') (m : ℤ),
  (∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0)) →
  (DerivedCategory.homologyFunctor (SShv B q) m).map f = 0

def LeafShIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (L K : DerivedCategory (SShv B q)) (ℓ : L ⟶ K) (m : ℤ),
  (∀ (U : B.Etale) (x x' : (OU B q).obj U ⟶ (shiftFunctor _ m).obj L),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map ℓ = (OU B q).map a ≫ x' ≫ (shiftFunctor _ m).map ℓ) →
    Cov U (fun U' a => (OU B q).map a ≫ x = (OU B q).map a ≫ x')) →
  (∀ (U : B.Etale) (y : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ (shiftFunctor _ m).obj L, (OU B q).map a ≫ y = x ≫ (shiftFunctor _ m).map ℓ)) →
  IsIso ((DerivedCategory.homologyFunctor (SShv B q) m).map ℓ)

def LeafVan0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 2 < m → ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m,
  Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafKill2 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) 2,
  Cov U (fun U' a => rY q i (g1 ≫ p) ι a 2 (gY q i p g1 ι U 2 y) = 0)

def LeafKill1 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0)

def LeafVanB : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 0 < m → ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m,
  Cov U (fun U' a => rB q i ι a m c = 0)

def LeafInj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  Cov U (fun U' a => rB q i ι a 0 c = 0)

def LeafSurj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  Cov U (fun U' a => ∃ c : Hrel (ZMod q) (sch.map (prB ι U')) (tw q i) 0,
    bY q i (g2 ≫ g1 ≫ p) ι U' 0 c = rY q i (g2 ≫ g1 ≫ p) ι a 0 y)

theorem loc_zero_map {B : Scheme.{0}} {q : ℕ} {K K' : DerivedCategory (SShv B q)} (f : K ⟶ K') {m : ℤ}
    (X X' : B.Etale → Type 1) [∀ U, Zero (X' U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K))
    (e' : ∀ U, X' U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K'))
    (hb : ∀ U, Function.Surjective (e U))
    (res' : ∀ U U', (U' ⟶ U) → X' U → X' U') (φ : ∀ U, X U → X' U)
    (hnat : ∀ U U' (a : U' ⟶ U) y, e' U' (res' U U' a y) = (OU B q).map a ≫ e' U y)
    (hf : ∀ U y, e' U (φ U y) = e U y ≫ (shiftFunctor _ m).map f)
    (hv : ∀ U y, Cov U (fun U' a => res' U U' a (φ U y) = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0) := by
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  refine (Cov.and (hv U y) (hv U y0)).mono fun U' a ⟨h1, h2⟩ => ?_
  rw [← hf, ← hnat, h1, ← h2, hnat, hf, hy0, zero_comp, comp_zero]

theorem loc_zero {B : Scheme.{0}} {q : ℕ} {K : DerivedCategory (SShv B q)} {m : ℤ}
    (X : B.Etale → Type 1) [∀ U, Zero (X U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U))
    (res : ∀ U U', (U' ⟶ U) → X U → X U')
    (hnat : ∀ U U' (a : U' ⟶ U) y, e U' (res U U' a y) = (OU B q).map a ≫ e U y)
    (hv : ∀ U y, Cov U (fun U' a => res U U' a y = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0) :=
  loc_zero_map (𝟙 K) X X e e hb res (fun _ y => y) hnat (fun U y => by simp) hv U x

theorem isZero_of (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
      Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id]
  exact hZ B q K K (𝟙 K) m h

theorem isZero_neg (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (X : B.Etale → Type 1) (hs : ∀ U, Subsingleton (X U))
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  refine isZero_of hZ K m fun U x => Cov.all fun U' a => ?_
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  rw [Subsingleton.elim y y0, hy0]
  simp

theorem goal_of (hN : LeafNeg) (hZ : LeafShMapZero) (hI : LeafShIso) (hV0 : LeafVan0) (hK2 : LeafKill2)
    (hK1 : LeafKill1) (hVB : LeafVanB) (hIn : LeafInj0) (hSu : LeafSurj0) : LateralTheory.E.EtaleTopologySheaves.LeafDeg := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  have hS : SHV q i V p g1 g2 := hA
  refine ⟨fun m hm => ?_, ?_, ?_, fun m hm => ?_, fun m hm => ?_, ?_⟩
  · exact isZero_of hZ K0 m (loc_zero _ (l0 · m) (fun U => (r0.1 U m).2) (fun U U' a => rY q i p ι a m)
      (fun U U' a y => r0.2 U U' a m y) (fun U y => hV0 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm y))
  · exact hZ B q K0 K1 f 2 (loc_zero_map f _ _ (l0 · 2) (l1 · 2) (fun U => (r0.1 U 2).2)
      (fun U U' a => rY q i (g1 ≫ p) ι a 2) (fun U => gY q i p g1 ι U 2)
      (fun U U' a y => r1.2 U U' a 2 y) (fun U y => mf U 2 y)
      (fun U y => hK2 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact hZ B q K1 K2 g 1 (loc_zero_map g _ _ (l1 · 1) (l2 · 1) (fun U => (r1.1 U 1).2)
      (fun U U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1) (fun U => gY q i (g1 ≫ p) g2 ι U 1)
      (fun U U' a y => r2.2 U U' a 1 y) (fun U y => mg U 1 y)
      (fun U y => hK1 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact isZero_neg hZ K2 m _ (fun U => hN _ _ _ m hm) (l2 · m) (fun U => (r2.1 U m).2)
  · rcases lt_or_gt_of_ne hm with hm | hm
    · exact isZero_neg hZ L m _ (fun U => hN _ _ _ m hm) (lL · m) (fun U => (rL.1 U m).2)
    · exact isZero_of hZ L m (loc_zero _ (lL · m) (fun U => (rL.1 U m).2) (fun U U' a => rB q i ι a m)
        (fun U U' a c => rL.2 U U' a m c) (fun U c => hVB hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm c))
  · refine hI B q L K2 ℓ 0 (fun U x x' hx => ?_) (fun U y => ?_)
    · obtain ⟨c, rfl⟩ := (rL.1 U 0).2 x
      obtain ⟨c', rfl⟩ := (rL.1 U 0).2 x'
      have hd := hIn hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U (c - c') (hx.mono fun U' a h => by
        rw [← mℓ U 0 c, ← mℓ U 0 c', ← r2.2 U U' a 0, ← r2.2 U U' a 0] at h
        rw [map_sub, map_sub, (r2.1 U' 0).1 h, sub_self])
      refine hd.mono fun U' a h => ?_
      rw [← rL.2 U U' a 0 c, ← rL.2 U U' a 0 c', sub_eq_zero.1 ((map_sub _ c c').symm.trans h)]
    · obtain ⟨z, rfl⟩ := (r2.1 U 0).2 y
      refine (hSu hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U z).mono fun U' a ⟨c, hc⟩ => ⟨lL U' 0 c, ?_⟩
      rw [← r2.2 U U' a 0 z, ← hc, mℓ U' 0 c]

end LateralTheory.E.LeafDegCut
