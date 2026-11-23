import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSquareSqMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

theorem tanScal_iff {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] (A' : Over S')
    [GrpObj A'] (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A')
    (h : IsGrpPullback A' A f φ) (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (R' : Type) [CommRing R']
    (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A)
    (hv : v₀.left = v.left ≫ φ) :
    GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀ := by
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ :=
    (congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))).symm
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : (v₀ ≫ act.act b).left = (v ≫ act'.act b).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, hv, Category.assoc, Category.assoc, hact]
  refine and_congr ?_ ?_
  · rw [one, hv]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [E, hv]
    refine ⟨fun E' => by rw [E']; exact Category.assoc _ _ _,
      fun E' => h.1.hom_ext (E'.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem kerGen {S S' : Scheme.{0}} {f : S' ⟶ S} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A f φ) (P : LB (G2 A).left) (T : Over S') (x : T ⟶ A')
    (ht : ∃ t : ((P.pull (sqMap h.1.w)).pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A (Over.mk (T.hom ≫ f)) ≫ pushPt h.1.w x) (fst A (Over.mk (T.hom ≫ f)))).left).Gen,
      t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z' : Over S' := Over.mk ((snd A T₀).left ≫ T.hom)
  have eq : (fst A T₀).left ≫ A.hom = Z'.hom ≫ f :=
    (Over.w (fst A T₀)).trans ((Over.w (snd A T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a' : Z' ⟶ A' := Over.homMk (h.1.lift (fst A T₀).left Z'.hom eq) (h.1.lift_snd _ _ _)
  let t' : Z' ⟶ T := Over.homMk (snd A T₀).left rfl
  let u : Over.mk (Z'.hom ≫ f) ⟶ A ⊗ T₀ := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (A ⊗ T₀).hom = ((snd A T₀).left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (snd A T₀)).symm)
  have hc : (lift (t' ≫ x) a').left ≫ sqMap h.1.w = u.left ≫ (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left :=
    sqMap_of h.1.w u _ _ _ _ (Over.OverMorphism.ext (by
      show ((snd A T₀).left ≫ x.left) ≫ φ = 𝟙 _ ≫ (snd A T₀).left ≫ x.left ≫ φ
      rw [Category.id_comp, Category.assoc]))
      (Over.OverMorphism.ext (by
        show h.1.lift (fst A T₀).left Z'.hom eq ≫ φ = 𝟙 _ ≫ (fst A T₀).left
        rw [Category.id_comp, h.1.lift_fst]))
  have hψ : (lift a' t').left ≫ (lift (snd A' T ≫ x) (fst A' T)).left = (lift (t' ≫ x) a').left := by
    rw [← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst]
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => sqMap h.1.w) (fun _ => 1)
    (lift (snd A' T ≫ x) (fst A' T)).left) t ht
  refine gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left)
    (fun _ => (lift (snd A' T ≫ x) (fst A' T)).left ≫ sqMap h.1.w) (fun _ => 1) (lift a' t').left fun _ => ?_) t₁ ht₁
  rw [← Category.assoc, hψ, hc]
  exact (Category.id_comp _).symm

end GlobalTheory.UPel.HT.Pull

namespace GlobalTheory.UPel.HT.Pull

open GlobalTheory.UPel.HT

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  have h := isGrpPullback_pullback o.A f
  have hact := OActN.pullback_left f o.A o.act
  have w := h.1.w
  let A' := (Over.pullback f).obj o.A
  let φ := pullback.fst o.A.hom f
  let act' := OActN.pullback f o.A o.act
  let φ₂ := sqMap w
  let P' := o.P.pull φ₂
  let u : Over.mk (A'.hom ≫ f) ⟶ o.A := Over.homMk φ w
  let U : Over.mk ((G2 A').hom ≫ f) ⟶ G2 o.A := lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))
  have pa : ∀ {T : Over S'} (x : T ⟶ A') c, pushPt w (x ≫ act'.act c) = pushPt w x ≫ o.act.act c := fun x c =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have p1 : ∀ (T : Over S'), pushPt w (1 : T ⟶ A') = 1 := fun T => map_one (pushHom h T)
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂

  have hΔ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have hL : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullOut o.P (fun _ => φ₂) (fun _ => 1) _ (fun _ => _ ≫ φ₂) fun _ => rfl)
      (chartPullOut o.P (fun _ => _) (fun _ => 1) φ (fun _ => _ ≫ φ₂) fun _ => hΔ)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _))
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A A' f φ
    _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab h hL

  have r₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ ((p1 A').trans (MonObj.comp_one u).symm) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have r₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) ((p1 A').trans (MonObj.comp_one u).symm)
  have sw : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd o.A o.A) (fst o.A o.A)).left :=
    sqMap_of w U _ _ _ _ (lift_snd _ _).symm (lift_fst _ _).symm
  have ro : ∀ c : D.O, (lift (fst A' A' ≫ act'.act c) (snd A' A')).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left := fun c =>
    sqMap_of w U _ _ _ _ (by rw [pa, ← Category.assoc, lift_fst]) (lift_snd _ _).symm
  have ro' : ∀ c : D.O, (lift (fst A' A') (snd A' A' ≫ act'.act c)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act c)).left := fun c =>
    sqMap_of w U _ _ _ _ (lift_fst _ _).symm (by rw [pa, ← Category.assoc, lift_snd])
  have pul : ∀ {Y : Scheme.{0}} (g' : Y ⟶ (G2 A').left) {Y₀ : Scheme.{0}} (k : Y ⟶ Y₀) (g₀ : Y₀ ⟶ (G2 o.A).left), g' ≫ φ₂ = k ≫ g₀ → ChartPull (P'.pull g') (o.P.pull g₀) k :=
    fun g' _ k g₀ e => chartPullLinComb o.P φ₂ (fun _ => g') (fun _ => g₀) (fun _ => 1) k fun _ => e
  refine ⟨{ A := A'
            ab := hab
            act := act'
            P := P'
            isLB := hP'
            rig₁ := ?_
            rig₂ := ?_
            symm := ?_
            ample := hamp o.ample
            kerP := ?_
            rosati := ?_
            lie := ?_
            lieRank := ?_
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun x y => by rw [o.eta_add, map_mul]
            eta_lin := ?_
            eta_ker := fun x => by rw [o.eta_ker, map_one]
            geom := ?_ },
    ⟨{ φ := φ
       φ₂ := φ₂
       cart := h
       sq := isSquare_sqMap w
       act := hact
       pol := GlobalTheory.PolBaseChange.lbIso_refl hP'
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (pul _ φ _ r₁) t ht
  · obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (pul _ φ _ r₂) t ht
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P φ₂ φ₂ rfl) (pul _ φ₂ _ sw) o.symm
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x hx => ?_⟩
    have h0 := hk _ (pushPt w x) (kerGen o.A A' φ h o.P T x hx)
    apply (GlobalTheory.ObjPull.pushEquiv h T).injective
    rw [map_pow, map_one]
    exact h0
  · intro c
    exact LBIso.chartPull (pul _ φ₂ _ (ro c)) (pul _ φ₂ _ (ro' _)) (o.rosati c)
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    have key := fun (c : D.O) (r : R') (v : epsPtR x ⟶ A') =>
      tanScal_iff f o.A A' φ o.act act' h hact R' x c r v (e v) (he v)
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc]; exact hx) (e v) ((key _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (key _ _ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hw₀ i c), ?_⟩
    apply e.injective
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · intro k _ _ x β hx i
    exact (GlobalTheory.LiePull.lieMult_pull _ S S' o.A A' f φ (o.act.toF D) (act'.toF D) h (fun c => hact _) k x _ _).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc]; exact hx) i)
  · intro c y
    rw [o.eta_lin]
    apply (GlobalTheory.ObjPull.pushEquiv h _).injective
    apply Over.OverMorphism.ext
    show (GlobalTheory.ObjPull.secPull h (o.eta y ≫ o.act.act c)).left ≫ φ =
      (GlobalTheory.ObjPull.secPull h (o.eta y) ≫ act'.act c).left ≫ φ
    rw [GlobalTheory.ObjPull.secPull_left, Over.comp_left, Over.comp_left, Category.assoc, hact,
      reassoc_of% (GlobalTheory.ObjPull.secPull_left h (o.eta y))]
  · intro k _ _ x β hx
    obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc]; exact hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ φ = (g.left ≫ φ) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) h hL
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · rw [tateMoveO_ev]
      exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.Pull
