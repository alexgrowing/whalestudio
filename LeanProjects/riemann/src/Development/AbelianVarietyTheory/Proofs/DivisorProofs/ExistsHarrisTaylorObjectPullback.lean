import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.BaseChange

open ReciprocityTheory.ChartRestriction.G.Pdiv

section SlopeTestRemainingChoices

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pull {O : Type} [Ring O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OActN O G) :
    OActN O ((Over.pullback f).obj G) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pull_left {O : Type} [Ring O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OActN O G) (c : O) :
    ((OActN.pull f a).act c).left ≫ PullbackComparison.pφ f G = PullbackComparison.pφ f G ≫ (a.act c).left :=
  PullbackComparison.pullback_map_left_fst' f (a.act c)

theorem lift_pφ₂ {G : Over S} [GrpObj G] [IsCommMonObj G] {T' : Over S'} {T : Over S} (τ : T'.left ⟶ T.left)
    (a b : T' ⟶ (Over.pullback f).obj G) (a₀ b₀ : T ⟶ G)
    (ha : a.left ≫ PullbackComparison.pφ f G = τ ≫ a₀.left) (hb : b.left ≫ PullbackComparison.pφ f G = τ ≫ b₀.left) :
    (lift a b).left ≫ PullbackComparison.pφ₂ f G = τ ≫ (lift a₀ b₀).left := by
  apply PullbackComparison.adelic_GL2_ext_of_local_components
  · rw [Category.assoc, PullbackComparison.pφ₂_fst, ← Category.assoc, ← Over.comp_left, lift_fst, ha, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, PullbackComparison.pφ₂_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hb, Category.assoc,
      ← Over.comp_left, lift_snd]

end SlopeTestRemainingChoices

section Aux2

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def tateMoveO {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIsoO D k Q act e) : TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem isTanScal_push {O : Type} [Ring O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OActN O G) (a' : OActN O G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ G') ≃* (epsPtR (x ≫ f) ⟶ G)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ G') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    rw [← E, he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ a'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem secPull_comp {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u : G ⟶ G) (u' : G' ⟶ G') (hu : u'.left ≫ φ = φ ≫ u.left)
    (s : 𝟙_ (Over S) ⟶ G) : GlobalTheory.ObjPull.secPull h (s ≫ u) = GlobalTheory.ObjPull.secPull h s ≫ u' := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext ?_ ?_
  · rw [GlobalTheory.ObjPull.secPull_left]
    simp only [Over.comp_left, Category.assoc]
    rw [hu, ← Category.assoc (Over.Hom.left _) φ, GlobalTheory.ObjPull.secPull_left, Category.assoc]
  · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]

end Aux2

section Ker

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem gen_ker_push {G : Over S} [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (T : Over S')
    (x : T ⟶ (Over.pullback f).obj G)
    (H : ∃ t : ((P.pull (PullbackComparison.pφ₂ f G)).pull
      (lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd G (Over.mk (T.hom ≫ f)) ≫ GlobalTheory.ObjPull.pushEquiv (PullbackComparison.isGrpPullback f G) T x)
      (fst G (Over.mk (T.hom ≫ f)))).left).Gen, t.IsGen := by
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z : Over S' := Over.mk ((snd G T₀).left ≫ T.hom)
  have hZ : (fst G T₀).left ≫ G.hom = Z.hom ≫ f :=
    (Over.w (fst G T₀)).trans ((Over.w (snd G T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a : Z ⟶ (Over.pullback f).obj G := Over.homMk (pullback.lift (fst G T₀).left Z.hom hZ) (pullback.lift_snd _ _ _)
  let u : Z ⟶ T := Over.homMk (snd G T₀).left rfl
  have key : (lift (snd G T₀ ≫ GlobalTheory.ObjPull.pushEquiv (PullbackComparison.isGrpPullback f G) T x) (fst G T₀)).left =
      (lift a u).left ≫ ((lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left ≫
        PullbackComparison.pφ₂ f G) := by
    apply PullbackComparison.adelic_GL2_ext_of_local_components
    · have k1 := congrArg Over.Hom.left (show lift a u ≫ lift (snd ((Over.pullback f).obj G) T ≫ x)
          (fst ((Over.pullback f).obj G) T) ≫ fst ((Over.pullback f).obj G) ((Over.pullback f).obj G) = u ≫ x by simp)
      simp only [Over.comp_left] at k1
      rw [← Over.comp_left, lift_fst, Category.assoc, Category.assoc, PullbackComparison.pφ₂_fst,
        ← Category.assoc (Over.Hom.left (lift (snd ((Over.pullback f).obj G) T ≫ x) _)), ← Category.assoc, k1]
      rfl
    · have k2 := congrArg Over.Hom.left (show lift a u ≫ lift (snd ((Over.pullback f).obj G) T ≫ x)
          (fst ((Over.pullback f).obj G) T) ≫ snd ((Over.pullback f).obj G) ((Over.pullback f).obj G) = a by simp)
      simp only [Over.comp_left] at k2
      rw [← Over.comp_left, lift_snd, Category.assoc, Category.assoc, PullbackComparison.pφ₂_snd,
        ← Category.assoc (Over.Hom.left (lift (snd ((Over.pullback f).obj G) T ≫ x) _)), ← Category.assoc, k2]
      exact (pullback.lift_fst _ _ _).symm
  obtain ⟨t, ht⟩ := H
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => PullbackComparison.pφ₂ f G) (fun _ => 1)
    (lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left) t ht
  exact gen_chartPull (chartPullSame P _ _ (fun _ : PUnit => 1) (lift a u).left (fun _ => key)) t₁ ht₁

end Ker

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (f : S' ⟶ S), f ≫ s = s' →
    ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s s' o f hs
  subst hs
  have h : IsGrpPullback ((Over.pullback f).obj o.A) o.A f (PullbackComparison.pφ f o.A) := PullbackComparison.isGrpPullback f o.A
  have hact := OActN.pull_left f o.act
  have hP := pull_isLB o.isLB (PullbackComparison.pφ₂ f o.A)
  have hL := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have hL' := pull_isLB hP (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left
  have hdiag : (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left ≫ PullbackComparison.pφ₂ f o.A =
      PullbackComparison.pφ f o.A ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    lift_pφ₂ f _ _ _ _ _ (by simp) (by simp)
  have hLi : LBIso ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull
      (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left)
      ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull (PullbackComparison.pφ f o.A)) :=
    LBIso.chartPull (chartPullLinComb o.P (PullbackComparison.pφ₂ f o.A) _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ f o.A) (fun _ => hdiag))
      (chartPullPull _ (PullbackComparison.pφ f o.A) _ rfl) (PullbackComparison.gen_refl _ hL)
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A _ f _
    _ _ hL hL' o.ab h hLi
  have hrose : ∀ c : D.O, LBIso ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull
      (lift (fst ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A) ≫ (OActN.pull f o.act).act c)
        (snd ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A))).left)
      ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull (lift (fst ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A))
        (snd ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A) ≫
          (OActN.pull f o.act).act (D.star c).unop)).left) := fun c => by
    refine LBIso.chartPull (chartPullLinComb o.P _ _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ₂ f o.A) (fun _ => ?_))
      (chartPullLinComb o.P _ _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ₂ f o.A) (fun _ => ?_)) (o.rosati c)
    · refine lift_pφ₂ f _ _ _ _ _ ?_ (PullbackComparison.pφ₂_snd f o.A).symm
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← PullbackComparison.pφ₂_fst, Category.assoc]
    · refine lift_pφ₂ f _ _ _ _ _ (PullbackComparison.pφ₂_fst f o.A).symm ?_
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← PullbackComparison.pφ₂_snd, Category.assoc]
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  refine ⟨{ A := (Over.pullback f).obj o.A
            ab := hab
            act := OActN.pull f o.act
            P := o.P.pull (PullbackComparison.pφ₂ f o.A)
            isLB := hP
            rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
              (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
            rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
              (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
            symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
              (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ₂ f o.A) (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
            ample := hamp o.ample
            kerP := ?_
            rosati := hrose
            lie := ?_
            lieRank := fun k _ _ x β hx i =>
              (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A _ f _ (o.act.toF D) ((OActN.pull f o.act).toF D) h
                (fun c => hact _) k x (β.comp (b.t i)) D.m).2
                (o.lieRank k (x ≫ f) β ((Category.assoc _ _ _).trans hx) i)
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun y z => by rw [o.eta_add, map_mul]
            eta_lin := fun c y => by rw [o.eta_lin]; exact secPull_comp f h _ _ (hact c) _
            eta_ker := fun y => by rw [o.eta_ker y, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨{ φ := PullbackComparison.pφ f o.A
       φ₂ := PullbackComparison.pφ₂ f o.A
       cart := h
       sq := PullbackComparison.isSquare f o.A
       act := hact
       pol := PullbackComparison.gen_refl _ hP
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x H => ?_⟩
    have := hk (Over.mk (T.hom ≫ f)) (GlobalTheory.ObjPull.pushEquiv h T x) (gen_ker_push f o.P T x H)
    exact (GlobalTheory.ObjPull.pushEquiv h T).injective (by rw [map_pow, this, map_one])
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) ((Category.assoc _ _ _).trans hx) (e v)
      ((isTanScal_push f h o.act _ hact x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (isTanScal_push f h o.act _ hact x e he _ _ _).2
      (by rw [e.apply_symm_apply]; exact hw₀ i c), e.injective ?_⟩
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β ((Category.assoc _ _ _).trans hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f _ _ _ hL hL' h hLi
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.BaseChange
