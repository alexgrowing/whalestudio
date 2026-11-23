import Development.EtaleCohomology.EtaleSheaves.LeafVanBPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBStalkPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c1 : f' ≫ e = u ≫ f) (c2 : f'' ≫ e' = u' ≫ f')
    (c3 : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c3 = rmap R f' f'' u' e' c2 ≫ rmap R f f' u e c1 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [mappingCone.ext_from_iff _ (n + 1) n rfl]
  simp [rmap, mappingCone.map]

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c1 : f' ≫ e = u ≫ f) (c2 : f'' ≫ e' = u' ≫ f')
    (c3 : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) c3 F n y = rpull R f' f'' u' e' c2 F n (rpull R f f' u e c1 F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' c1 c2 c3, hkpull_comp]

theorem rpull_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u₀ : U' ⟶ U}
    {e e₀ : E' ⟶ E} (hu : u = u₀) (he : e = e₀) (c : f' ≫ e = u ≫ f) (c₀ : f' ≫ e₀ = u₀ ≫ f) (F : Shv R) (n : ℤ) :
    rpull R f f' u e c F n = rpull R f f' u₀ e₀ c₀ F n := by
  subst hu he; rfl

theorem rB_comp (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' U'' : B.Etale} (a : U' ⟶ U) (b : U'' ⟶ U')
    (m : ℤ) (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m) :
    rB q i ι (b ≫ a) m c = rB q i ι b m (rB q i ι a m c) := by
  have h1 : resBW ι (b ≫ a) = resBW ι b ≫ resBW ι a := by
    apply pullback.hom_ext <;>
      simp only [resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc] <;> rfl
  have h2 : (b ≫ a).left = b.left ≫ a.left := rfl
  simp only [rB, rpl]
  rw [rpull_congr (ZMod q) _ _ (show sch.map (resBW ι (b ≫ a)) = sch.map (resBW ι b) ≫ sch.map (resBW ι a) by
      rw [h1, Functor.map_comp])
    (show sch.map (b ≫ a).left = sch.map b.left ≫ sch.map a.left by rw [h2, Functor.map_comp]) _
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← h1, ← h2,
      pullback.lift_fst])]
  exact rpull_comp (ZMod q) _ _ _ _ _ _ _ _ _ _ (tw q i) m c

structure SHSys {B : Scheme.{0}} (U : B.Etale) (x : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  e : ∀ j, (V j).left ≅ Spec (D.obj j)
  tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j
  tr_a : ∀ {j j' : J} (g : j ⟶ j'), tr g ≫ a j = a j'
  tr_spec : ∀ {j j' : J} (g : j ⟶ j'), (e j').inv ≫ (tr g).left ≫ (e j).hom = Spec.map (D.map g)
  hx : ∀ j, x ∈ Set.range (a j).left
  c : Cocone D
  hc : IsColimit c
  sh : SH c.pt
  t : Spec c.pt ⟶ U.left
  ht : ∀ j, t = Spec.map (c.ι.app j) ≫ (e j).inv ≫ (a j).left

attribute [instance] SHSys.cat SHSys.filt

def LeafSHSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left), Nonempty (SHSys U x)

def LeafSHCont : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m) (x : U.left) (S : SHSys U x),
  bpl q i ι U S.t m c = 0 → ∃ j, rB q i ι (S.a j) m c = 0

def LeafStalkPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  ∀ x : U.left, ∃ (V : B.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ rB q i ι a m c = 0

theorem cov_of_pts {B W : Scheme.{0}} (q : ℕ) (i : ℤ) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m)
    (h : ∀ x : U.left, ∃ (V : B.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ rB q i ι a m c = 0) :
    Cov U (fun _ a => rB q i ι a m c = 0) := by
  choose V a hx hz using h
  refine ⟨Sieve.ofArrows V a, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, hx x⟩
  · intro U' g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨x, b, rfl⟩ := hg
    rw [rB_comp, hz x, map_zero]

theorem stalkPt_of (hN : LeafSHSys) (hC : LeafSHCont) : LeafStalkPt := by
  intro hy q _ k _ hq i B W s ι _ U m c hc x
  obtain ⟨S⟩ := hN U x
  have hu : IsUnit (q : S.c.pt) := by
    have g := Spec.preimage (S.t ≫ U.hom ≫ s)
    simpa using hq.map g.hom
  haveI : IsLocalRing S.c.pt := S.sh.1.toIsLocalRing
  have h0 := hc S.c.pt S.t S.sh hu
  obtain ⟨j, hj⟩ := hC hy q k hq i s ι U m c x S h0
  exact ⟨S.V j, S.a j, S.hx j, hj⟩

theorem LeafVanBStalk_of (hN : LeafSHSys) (hC : LeafSHCont) : LeafVanBStalk := by
  have hP := stalkPt_of hN hC
  intro hy q _ k _ hq i B W s ι _ U m c hc
  exact cov_of_pts q i ι U m c (hP hy q k hq i s ι U m c hc)

theorem LeafVanBStalk_of_pt (hP : LeafStalkPt) : LeafVanBStalk := by
  intro hy q _ k _ hq i B W s ι _ U m c hc
  exact cov_of_pts q i ι U m c (hP hy q k hq i s ι U m c hc)

end LateralTheory.E.LeafVanBStalkPf
