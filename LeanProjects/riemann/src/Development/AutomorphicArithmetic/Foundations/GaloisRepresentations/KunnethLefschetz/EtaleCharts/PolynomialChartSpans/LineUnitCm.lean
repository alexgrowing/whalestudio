import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PBEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PBOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassEqZeroOfUnitTrivialization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G.PBEPf

variable {A B C D : Scheme.{0}} {e : A ⟶ C} {f : B ⟶ D}

private def vx (f : B ⟶ D) (i : Fin 2) {U : Scheme.{0}} (x : Sx (cech f) 1 U) : U ⟶ B :=
  (WidePullback.π (fun _ : Fin 2 => yoneda.map f) i).app (op U) x

private def vtx (f : B ⟶ D) {U : Scheme.{0}} (x : Sx (cech f) 0 U) : U ⟶ B :=
  (WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0).app (op U) x

private theorem vtx_res (g : B ⟶ D) {U U' : Scheme.{0}} (k : U' ⟶ U) (x : Sx (cech g) 0 U) :
    vtx g (((cech g).obj (op (SimplexCategory.mk 0))).map k.op x) = k ≫ vtx g x := by
  unfold vtx
  exact NatTrans.naturality_apply (WidePullback.π (fun _ : Fin 1 => yoneda.map g) 0) k.op x

private theorem vtx_face (g : B ⟶ D) {U : Scheme.{0}} (x : Sx (cech g) 1 U) (i : Fin 2) :
    vtx g (((cech g).map (SimplexCategory.δ (n := 0) i).op).app (op U) x) = vx g (1 - i) x := by
  have h := ConcreteCategory.congr_hom (congr_app (WidePullback.lift_π (fun _ : Fin 1 => yoneda.map g)
    (WidePullback.base (fun _ : Fin 2 => yoneda.map g))
    (fun k : Fin 1 => WidePullback.π (fun _ : Fin 2 => yoneda.map g) ((SimplexCategory.δ (n := 0) i).toOrderHom k))
    (fun _ => WidePullback.π_arrow _ _) (0 : Fin 1)) (op U)) x
  unfold vtx vx
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  · fin_cases i <;> rfl

private def sq (τ : A ⟶ B) (j : C ⟶ D) (w : τ ≫ f = e ≫ j) :
    Arrow.mk (yoneda.map e) ⟶ Arrow.mk (yoneda.map f) :=
  Arrow.homMk (yoneda.map τ) (yoneda.map j) (by simp only [Arrow.mk_hom, ← Functor.map_comp, w])

private def cm (τ : A ⟶ B) (j : C ⟶ D) (w : τ ≫ f = e ≫ j) : cech e ⟶ cech f :=
  Arrow.mapCechNerve (sq τ j w)

private theorem cm_aug (τ : A ⟶ B) (j : C ⟶ D) (w : τ ≫ f = e ≫ j) :
    cm τ j w ≫ cechAug f = cechAug e ≫ sch.map j :=
  (Arrow.mapAugmentedCechNerve (sq τ j w)).w

private theorem vx_cm (τ : A ⟶ B) (j : C ⟶ D) (w : τ ≫ f = e ≫ j) {V : Scheme.{0}} (x : Sx (cech e) 1 V) (i : Fin 2) :
    vx f i (((cm τ j w).app (op (SimplexCategory.mk 1))).app (op V) x) = vx e i x ≫ τ := by
  have h := ConcreteCategory.congr_hom (congr_app (WidePullback.lift_π (fun _ : Fin 2 => yoneda.map f)
    (WidePullback.base (fun _ : Fin 2 => yoneda.map e) ≫ yoneda.map j)
    (fun k : Fin 2 => WidePullback.π (fun _ : Fin 2 => yoneda.map e) k ≫ yoneda.map τ)
    (fun k => by rw [Category.assoc, ← Functor.map_comp, w, Functor.map_comp, ← Category.assoc,
      WidePullback.π_arrow]) i) (op V)) x
  exact h

private theorem vx_pt {V : Scheme.{0}} (b : V ⟶ D) (a : Fin 2 → (V ⟶ B)) (h : ∀ i, a i ≫ f = b) (i : Fin 2) :
    vx f i (cechPt f 1 b a h) = a i := by
  have h' := ConcreteCategory.congr_hom (congr_app (WidePullback.lift_π (fun _ : Fin 2 => yoneda.map f)
    (yoneda.map b) (fun k => yoneda.map (a k)) (fun k => by rw [← yoneda.map_comp, h k]) i) (op V)) (𝟙 V)
  exact h'.trans (Category.id_comp (a i) : 𝟙 V ≫ a i = a i)

private theorem eta {V : Scheme.{0}} (x : Sx (cech f) 1 V) :
    ∃ (b : V ⟶ D) (h : ∀ i, vx f i x ≫ f = b), x = cechPt f 1 b (fun i => vx f i x) h := by
  let b : V ⟶ D := (WidePullback.base (fun _ : Fin 2 => yoneda.map f)).app (op V) x
  have hb : ∀ i, vx f i x ≫ f = b := fun i =>
    ConcreteCategory.congr_hom (congr_app (WidePullback.π_arrow (fun _ : Fin 2 => yoneda.map f) i) (op V)) x
  refine ⟨b, hb, ?_⟩
  let x' : (widePullback (yoneda.obj D) (fun _ : Fin 2 => yoneda.obj B) (fun _ => yoneda.map f)).obj (op V) := x
  have key : WidePullback.lift (arrows := fun _ : Fin 2 => yoneda.map f) (yoneda.map b) (fun i => yoneda.map (vx f i x))
      (fun i => by rw [← yoneda.map_comp, hb i]) = yonedaEquiv.symm x' := by
    apply WidePullback.hom_ext
    · intro i
      rw [WidePullback.lift_π]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
      rfl
    · rw [WidePullback.lift_base]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  unfold cechPt
  rw [key]
  exact (yonedaEquiv.apply_symm_apply x').symm

private theorem u_congr {X : Scheme.{0}} (L : E.LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ L.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ L.f = b ≫ L.f) (h' : a' ≫ L.f = b' ≫ L.f) : L.u a b h = L.u a' b' h' := by
  subst ha hb; rfl

private theorem lineUnit_cm {X : Scheme.{0}} (Dl : E.LineData X) {L : cech Dl.f ⟶ ofCat (glCat 1)} (hL : Dl.IsMap L)
    (τ : A ⟶ Dl.Y) (j : C ⟶ X) (w : τ ≫ Dl.f = e ≫ j) {V : Scheme.{0}} (x : Sx (cech e) 1 V)
    (h : (vx e 0 x ≫ τ) ≫ Dl.f = (vx e 1 x ≫ τ) ≫ Dl.f) :
    lineUnit (cm τ j w ≫ L) x = Dl.u (vx e 0 x ≫ τ) (vx e 1 x ≫ τ) h := by
  change lineUnit L (((cm τ j w).app (op (SimplexCategory.mk 1))).app (op V) x) = _
  obtain ⟨b, hb, hy⟩ := eta (((cm τ j w).app (op (SimplexCategory.mk 1))).app (op V) x)
  have h1 := hL V b _ hb
  rw [← hy] at h1
  rw [h1]
  exact u_congr Dl (vx_cm τ j w x 0) (vx_cm τ j w x 1) _ _

private theorem inv_cech {K : Type} [CommRing K] {q : ℕ} (hq : IsUnit (q : K)) (g : B ⟶ D)
    (p : D ⟶ Spec (CommRingCat.of K)) : GlobalTheory.EtC.Inv q (cech g) := by
  intro U ⟨x⟩
  have h := hq.map (((vtx g x ≫ g ≫ p).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  simpa using h

end UpperTheory.Gal.KunnethLefschetz.G.PBEPf

open UpperTheory.Gal.KunnethLefschetz.G.PBEPf in
theorem UpperTheory.Gal.KunnethLefschetz.G.pBE :
    UpperTheory.Gal.KunnethLefschetz.G.PBE := by
  intro hI q _ K _ hq W Z Y T p i π D d hB j r hpb L hL x hx
  have hinvD : GlobalTheory.EtC.Inv q (cech D.f) := inv_cech hq D.f (π ≫ p)
  refine ⟨?_, ?_⟩
  · obtain ⟨P, τ, hτ, hw⟩ := UpperTheory.Gal.KunnethLefschetz.G.pBEx K p i π D d hB j r hpb
    have hqW : IsUnit (q : Γ(W, ⊤)) := by
      have h := hq.map (((i ≫ p).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      simpa using h
    have hx' : pull _ (cechAug P.e) _ 2 (pull _ (sch.map j) _ 2 x) = c1 q (cm τ j hτ ≫ L) := by
      rw [← pull_comp, ← cm_aug τ j hτ, pull_comp, hx]
      exact (hI.a6nat q).2.2.1 _ L hinvD
    refine UpperTheory.Gal.KunnethLefschetz.G.pBOf hI q r d P hqW (cm τ j hτ ≫ L) (-1) ?_ _ hx'
    intro V t a h
    have e0 : vx P.e 0 (cechPt P.e 1 t a h) = a 0 := vx_pt t a h 0
    have e1 : vx P.e 1 (cechPt P.e 1 t a h) = a 1 := vx_pt t a h 1
    have h' : (a 0 ≫ τ) ≫ D.f = (a 1 ≫ τ) ≫ D.f := by
      simp only [Category.assoc, hτ]
      rw [← Category.assoc, ← Category.assoc, h 0, h 1]
    have h'' : (vx P.e 0 (cechPt P.e 1 t a h) ≫ τ) ≫ D.f = (vx P.e 1 (cechPt P.e 1 t a h) ≫ τ) ≫ D.f := by
      rw [e0, e1]; exact h'
    rw [lineUnit_cm D hL τ j hτ _ h'', u_congr D (by rw [e0]) (by rw [e1]) h'' h',
      hw (a 0) (a 1) ((h 0).trans (h 1).symm) h']
    simp
  · intro U hU
    obtain ⟨Bl⟩ := hB
    haveI := D.sm
    haveI := D.surj
    have hun : ∀ {V : Scheme.{0}} (a : V ⟶ pullback D.f U.ι), IsUnit (Bl.f (a ≫ pullback.fst D.f U.ι)) := by
      intro V a
      refine Bl.unit _ ?_
      intro v _
      change ((a ≫ pullback.fst D.f U.ι) ≫ D.f ≫ π) v ∈ Bl.U
      have e1 : (a ≫ pullback.fst D.f U.ι) ≫ D.f ≫ π = ((a ≫ pullback.snd D.f U.ι) ≫ U.ι) ≫ π := by
        simp only [Category.assoc]
        rw [pullback.condition_assoc]
      rw [e1]
      have hy : ((a ≫ pullback.snd D.f U.ι) ≫ U.ι) v ∈ (U : Set Y) := by
        rw [← Scheme.Opens.range_ι]
        exact ⟨(a ≫ pullback.snd D.f U.ι) v, by simp⟩
      rw [← SetLike.mem_coe, Bl.U_eq]
      rintro ⟨w', hw'⟩
      have hy' := hy
      rw [hU] at hy'
      apply hy'
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := π) (g := i) (((a ≫ pullback.snd D.f U.ι) ≫ U.ι) v) w' (by rw [hw']; simp)
      refine ⟨hpb.isoPullback.inv z, ?_⟩
      rw [← hz1, ← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst]
    let f' := pullback.snd D.f U.ι
    let s : ∀ V : Scheme.{0}, Sx (cech f') 0 V → (Γ(V, ⊤))ˣ := fun V t => (hun (vtx f' t)).unit
    have c : ∀ (V : Scheme.{0}) (t : Sx (cech f') 0 V),
        ((s V t : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) = Bl.f (vtx f' t ≫ pullback.fst D.f U.ι) := fun V t => IsUnit.unit_spec _
    have w : pullback.fst D.f U.ι ≫ D.f = f' ≫ U.ι := pullback.condition
    have hs : ∀ (V V' : Scheme.{0}) (g : V ⟶ V') (t : Sx (cech f') 0 V'),
        s V (Sx.res g t) = ClsSpec.umap g (s V' t) := by
      intro V V' g t
      apply Units.ext
      have h1 : vtx f' (Sx.res g t) = g ≫ vtx f' t := vtx_res f' g t
      change _ = g.appTop.hom ((s V' t : (Γ(V', ⊤))ˣ) : Γ(V', ⊤))
      rw [c, c, h1, Category.assoc, Bl.f_nat]
    have hLs : ∀ (V : Scheme.{0}) (t : Sx (cech f') 1 V),
        s V (t.face 1) = lineUnit (cm (pullback.fst D.f U.ι) U.ι w ≫ L) t * s V (t.face 0) := by
      intro V t
      apply Units.ext
      have a0 : vtx f' (t.face 1) = vx f' 0 t := vtx_face f' t 1
      have a1 : vtx f' (t.face 0) = vx f' 1 t := vtx_face f' t 0
      have hh : (vx f' 0 t ≫ pullback.fst D.f U.ι) ≫ D.f = (vx f' 1 t ≫ pullback.fst D.f U.ι) ≫ D.f := by
        obtain ⟨b, hb, -⟩ := eta t
        simp only [Category.assoc, w]
        rw [← Category.assoc, ← Category.assoc, hb, hb]
      rw [Units.val_mul, c, c, a0, a1, lineUnit_cm D hL (pullback.fst D.f U.ι) U.ι w t hh]
      exact Bl.f_u _ _ hh
    have hz : c1 q (cm (pullback.fst D.f U.ι) U.ι w ≫ L) = 0 :=
      ChartChern.firstChernClass_eq_zero_of_unit_trivialization q _ (inv_cech hq f' (U.ι ≫ π ≫ p)) s hs hLs
    have hz2 : pull _ (cechAug f') _ 2 (pull _ (sch.map U.ι) _ 2 x) = 0 := by
      rw [← pull_comp, ← cm_aug (pullback.fst D.f U.ι) U.ι w, pull_comp, hx]
      exact ((hI.a6nat q).2.2.1 _ L hinvD).trans hz
    exact (hI.a2 (ZMod q) f' (tw q 1) 2).1 (hz2.trans (map_zero _).symm)

end
