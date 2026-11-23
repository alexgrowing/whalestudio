import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TateGeneric

theorem push_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    {T : Over S'} {g : T.left ⟶ S} (e : (T ⟶ G') ≃* (Over.mk g ⟶ G)) (he : ∀ x, (e x).left = x.left ≫ φ)
    (u : G' ⟶ G') (v : G ⟶ G) (huv : u.left ≫ φ = φ ≫ v.left) (x : T ⟶ G') : e (x ≫ u) = e x ≫ v := by
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, huv, Category.assoc]

theorem push_comp_symm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    {T : Over S'} {g : T.left ⟶ S} (e : (T ⟶ G') ≃* (Over.mk g ⟶ G)) (he : ∀ x, (e x).left = x.left ≫ φ)
    (u : G' ⟶ G') (v : G ⟶ G) (huv : u.left ≫ φ = φ ≫ v.left) (y : Over.mk g ⟶ G) :
    e.symm (y ≫ v) = e.symm y ≫ u := by
  apply e.injective
  rw [push_comp e he u v huv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem weil_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) : Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c := by
  subst hg
  exact weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey

theorem lbIso_sab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem toUnit_left {S : Scheme.{0}} {W : Scheme.{0}} (x : W ⟶ S) : (toUnit (Over.mk x)).left = x := by
  have := Over.w (toUnit (Over.mk x))
  simpa using this

theorem exists_tateIso_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = zeta l.A → letI := H.starRing; ∃ J : TateIso D F (Out.TFK (R := T.V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a) (fun n g g' c => Out.WeilIs P.A.A P.A.L n g g' (unitOn c)), (J.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) ∧ (∀ a q, QkExt (algebraMap _ F) (hL.1 a).choose q → P.ToA F l.A q (J.ev l.A a)) ∧ ∀ a (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)), ∀ q, QkExt (algebraMap _ F) (hL.2 a ha).choose q → P.ToA F l.M q (J.ev l.M a) := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z h₁ h₂ h₃ h₄ t m P hL F _ _ _ r hr
  letI := H.starRing
  let β' : KA l →+* F := ((algebraMap T.Fr F).comp io).comp (IntermediateField.inclusion c.le).toRingHom
  let x : Sp F ⟶ Xo.XF c := spMap (algebraMap T.Fr F) ≫ z
  have hx : x ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β' := by
    change (spMap (algebraMap T.Fr F) ≫ z) ≫ pullback.fst _ _ ≫ Xo.s = _
    rw [pullback.condition, Category.assoc, reassoc_of% h₃]
    simp only [spMap, β', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hζ : β' (baseKA l).ζ = algebraMap T.Fr F (algebraMap T.V T.Fr (b r)) := by
    have e : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ζ = β r :=
      Subtype.ext (by simpa [baseKA] using hr.symm)
    have e₂ : io (β r) = algebraMap T.V T.Fr (b r) := (RingHom.congr_fun h₁ r).symm
    simp only [β', RingHom.comp_apply, e, e₂]
  obtain ⟨-, I, hIζ, hIA, hIM⟩ := Y.oF.geom F x β' hx
  have hw : x ≫ Y.j = (TF (R := T.V) F).hom ≫ y := by
    show (spMap (algebraMap T.Fr F) ≫ z) ≫ Y.j = (jFK (R := T.V) F ≫ jK T.V) ≫ y
    rw [Category.assoc, h₄, Category.assoc]
  have := P.A.isAb.comm
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK T.V))).congr
      (Category.id_comp _) rfl
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK T.V))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hLA : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK T.V)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V) ≫ (t.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv Y.m.cart (Over.mk x) (x ≫ Y.j) rfl
  obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (TF (R := T.V) F) (x ≫ Y.j) hw
  obtain ⟨e₃, he₃⟩ := GlobalTheory.LiePull.exists_pushEquiv gpG (TFK (R := T.V) F) (jFK (R := T.V) F ≫ jK T.V) rfl
  let e : (Over.mk x ⟶ Y.oF.t.G) ≃* (TFK (R := T.V) F ⟶ P.A.A) := e₁.trans (e₂.symm.trans e₃.symm)
  have he₂' : ∀ w, w.left = (e₂.symm w).left ≫ m.φ := fun w => by
    rw [← he₂, MulEquiv.apply_symm_apply]
  have he₃' : ∀ w, w.left = (e₃.symm w).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V) := fun w => by
    rw [← he₃, MulEquiv.apply_symm_apply]
  have hpt : ∀ g, (e g).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK T.V) ≫ m.φ = g.left ≫ Y.m.φ := fun g => by
    rw [← he₁, he₂' (e₁ g), he₃' (e₂.symm (e₁ g))]
    simp only [Category.assoc]; rfl
  have hact : ∀ a g, e (g ≫ Y.oF.t.act.act a) = e g ≫ P.oA.act a := fun a g => by
    show e₃.symm (e₂.symm (e₁ _)) = e₃.symm (e₂.symm (e₁ g)) ≫ _
    rw [push_comp e₁ he₁ _ _ (Y.m.act a), push_comp_symm e₂ he₂ _ _ (m.act a),
      push_comp_symm e₃ he₃ _ _ (actA a)]
  have hLY := lbIso_sab Y.m
  have hLm := lbIso_sab m
  refine ⟨
    { ζ := I.ζ
      ζ_prim := I.ζ_prim
      ζ_pow := I.ζ_pow
      ev := fun n a => e (I.ev n a)
      add := fun n a b => by simp only [I.add, map_mul]
      lin := fun n c a => by
        show e (I.ev n (c • a)) = e (I.ev n a) ≫ P.oA.act c
        rw [I.lin n c a, hact]
      ker := fun n hn a => (map_eq_one_iff e e.injective).trans (I.ker n hn a)
      onto := fun n hn w => by
        rw [← map_eq_one_iff e.symm e.symm.injective, map_pow, I.onto n hn]
        exact exists_congr fun a => e.eq_symm_apply
      tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
      isom := fun n hn a b => by
        have h := I.isom n hn a b
        have s1 := (weil_iff Y.t.PP.isLB Y.oF.t.PP.isLB Y.m.cart hLY (Over.mk x) (x ≫ Y.j) rfl n
          (I.ev n a) (I.ev n b) (e₁ (I.ev n a)) (e₁ (I.ev n b)) _ (he₁ _) (he₁ _)).1 h
        have s2 := (weil_iff Y.t.PP.isLB t.PP.isLB m.cart hLm (TF (R := T.V) F) (x ≫ Y.j) hw n
          (e₂.symm (e₁ (I.ev n a))) (e₂.symm (e₁ (I.ev n b))) (e₁ (I.ev n a)) (e₁ (I.ev n b)) _
          (he₂' _) (he₂' _)).2 s1
        exact (weil_iff t.PP.isLB P.A.isLB gpG hLA (TFK (R := T.V) F) (jFK (R := T.V) F ≫ jK T.V) rfl n
          (e (I.ev n a)) (e (I.ev n b)) (e₂.symm (e₁ (I.ev n a))) (e₂.symm (e₁ (I.ev n b))) _
          (he₃' _) (he₃' _)).2 s2 }, ?_, ?_, ?_⟩
  · show (I.ζ l.A : F) = _
    rw [hIζ, hζ]; rfl
  · intro a q hq
    refine (hL.1 a).choose_spec F x (hw.trans (Category.assoc _ _ _)) q _ hq ?_
    show (e (I.ev l.A a)).left ≫ _ = _
    rw [hpt, ← hIA a, Over.comp_left, toUnit_left, Category.assoc]
  · intro a ha q hq
    refine (hL.2 a ha).choose_spec F x (hw.trans (Category.assoc _ _ _)) q _ hq ?_
    show (e (I.ev l.M a)).left ≫ _ = _
    rw [hpt, ← hIM a ha, Over.comp_left, toUnit_left, Category.assoc]

end GlobalTheory.TateGeneric
