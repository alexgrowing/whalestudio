import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.HTPullEvery

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (pφ pφ₂ isSquare pφ₂_fst pφ₂_snd adelic_GL2_ext_of_local_components pullback_map_left_fst' isGrpPullback gen_refl)

section Grp

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem lift_pφ₂ (A : Over S) [GrpObj A] [IsCommMonObj A]
    (a' b' : G2 ((Over.pullback f).obj A) ⟶ (Over.pullback f).obj A) (a b : G2 A ⟶ A)
    (ha : a'.left ≫ pφ f A = pφ₂ f A ≫ a.left) (hb : b'.left ≫ pφ f A = pφ₂ f A ≫ b.left) :
    (lift a' b').left ≫ pφ₂ f A = pφ₂ f A ≫ (lift a b).left := by
  apply adelic_GL2_ext_of_local_components
  · rw [Category.assoc, pφ₂_fst, ← Category.assoc, ← Over.comp_left, lift_fst, ha, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, pφ₂_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hb, Category.assoc,
      ← Over.comp_left, lift_snd]

theorem map_left_pφ (A : Over S) [GrpObj A] [IsCommMonObj A] (g : A ⟶ A) :
    ((Over.pullback f).map g).left ≫ pφ f A = pφ f A ≫ g.left :=
  pullback_map_left_fst' f g

theorem push_map (A : Over S) [GrpObj A] [IsCommMonObj A] (g : A ⟶ A) :
    pushHom (isGrpPullback f A) _ ((Over.pullback f).map g) =
      (Over.homMk (pφ f A) pullback.condition : Over.mk (((Over.pullback f).obj A).hom ≫ f) ⟶ A) ≫ g :=
  Over.OverMorphism.ext (map_left_pφ f A g)

theorem gen_push {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂))
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A (Over.mk (T.hom ≫ f)) ≫ pushHom h T x) (fst A (Over.mk (T.hom ≫ f)))).left).Gen,
      t.IsGen := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

end Grp

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem tate_transport {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIsoO D k Q act e) (r : Q →* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hbij : ∀ n, 0 < n → n.Coprime p → Set.BijOn r {y : Q | y ^ n = 1} {y : Q' | y ^ n = 1})
    (hisom : ∀ n, 0 < n → n.Coprime p → ∀ x y, e' n (r (I.ev n x)) (r (I.ev n y)) (I.ζ n ^ (2 * D.EF x y))) :
    ∃ I' : TateIsoO D k Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) := by
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ x, I.ev n x ^ n = 1 :=
    fun n h1 h2 x => (I.onto n h1 h2 _).2 ⟨x, rfl⟩
  refine ⟨
    { ζ := I.ζ
      ζ_prim := I.ζ_prim
      ζ_pow := I.ζ_pow
      ev := fun n x => r (I.ev n x)
      add := fun n x y => by simp only [I.add, map_mul]
      lin := fun n c x => by simp only [I.lin, hact]
      ker := fun n h1 h2 x => ?_
      onto := fun n h1 h2 q => ?_
      tower := fun n m h1 h2 h3 x => by simp only [← map_pow, I.tower n m h1 h2 h3]
      isom := hisom }, fun n x => rfl⟩
  · rw [← I.ker n h1 h2 x]
    constructor
    · intro h
      refine (hbij n h1 h2).injOn (htor n h1 h2 x) (show (1 : Q) ^ n = 1 from one_pow n) ?_
      rw [h, map_one]
    · intro h
      show r (I.ev n x) = 1
      rw [h, map_one]
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := (hbij n h1 h2).surjOn hq
      obtain ⟨x, hx⟩ := (I.onto n h1 h2 y).1 hy
      exact ⟨x, by rw [hx]⟩
    · rintro ⟨x, rfl⟩
      show r (I.ev n x) ^ n = 1
      rw [← map_pow, htor n h1 h2 x, map_one]

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def actPull {A : Over S} [GrpObj A] [IsCommMonObj A] (a : OActN D.O A) : OActN D.O ((Over.pullback f).obj A) where
  act c := (Over.pullback f).map (a.act c)
  hom c := by have := a.hom c; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul b c := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add b c := by
    apply GlobalTheory.SiegelPull.push_injective (isGrpPullback f A)
    rw [map_mul, push_map, push_map, push_map, a.add, MonObj.comp_mul]

theorem actPull_left {A : Over S} [GrpObj A] [IsCommMonObj A] (a : OActN D.O A) (c : D.O) :
    ((actPull f a).act c).left ≫ pφ f A = pφ f A ≫ (a.act c).left :=
  map_left_pφ f A _

theorem isTanScal_pull {A : Over S} [GrpObj A] [IsCommMonObj A] (a : OActN D.O A) {R' : Type} [CommRing R']
    (x : Sp R' ⟶ S') (e : (epsPtR x ⟶ (Over.pullback f).obj A) ≃* (epsPtR (x ≫ f) ⟶ A))
    (he : ∀ v, (e v).left = v.left ≫ pφ f A) (c : D.O) (r : R') (v : epsPtR x ⟶ (Over.pullback f).obj A) :
    IsTanScal (actPull f a) x c r v ↔ IsTanScal a (x ≫ f) c r (e v) := by
  have h := isGrpPullback f A
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ pφ f A := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR r) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
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
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ (Over.pullback f).obj A)).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ (actPull f a).act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, actPull_left, Category.assoc])
    rw [← E, he, he]
    refine ⟨fun E' => by rw [E']; exact Category.assoc _ _ _,
      fun E' => h.1.hom_ext (E'.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ (actPull f a).act c)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR r) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

end GlobalTheory.HTPullEvery

namespace GlobalTheory.HTPullEvery

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (pφ pφ₂ isSquare pφ₂_fst pφ₂_snd adelic_GL2_ext_of_local_components pullback_map_left_fst' isGrpPullback gen_refl)

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R}

theorem push_act (f : S' ⟶ S) {A : Over S} [GrpObj A] [IsCommMonObj A] (a : OActN D.O A) {T : Over S'}
    (u : T ⟶ (Over.pullback f).obj A) (c : D.O) :
    pushHom (isGrpPullback f A) T (u ≫ (actPull f a).act c) = pushHom (isGrpPullback f A) T u ≫ a.act c :=
  Over.OverMorphism.ext (by
    show (u ≫ _).left ≫ pφ f A = (u.left ≫ pφ f A) ≫ _
    rw [Over.comp_left, Category.assoc, actPull_left, Category.assoc])

theorem geom_pull (o : Obj b N s) (f : S' ⟶ S) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S') (β : R →+* k) (hx : x ≫ s' = spMap β) :
    ∃ I : TateIsoO D k (Over.mk x ⟶ (Over.pullback f).obj o.A) (fun c g => g ≫ (actPull f o.act).act c)
        (fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
          ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y) = I.ev N y := by
    have h := isGrpPullback f o.A
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
    obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hs, hx])
    have hsymm : ∀ q, (e.symm q).left ≫ pφ f o.A = q.left := fun q => by rw [← he, e.apply_symm_apply]
    have hact : ∀ c q, e.symm.toMonoidHom (q ≫ o.act.act c) = e.symm.toMonoidHom q ≫ (actPull f o.act).act c := by
      intro c q
      apply e.injective
      show e (e.symm (q ≫ o.act.act c)) = e (e.symm q ≫ (actPull f o.act).act c)
      rw [e.apply_symm_apply]
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, Category.assoc, actPull_left, ← Category.assoc, hsymm]
    have hbij : ∀ n, 0 < n → n.Coprime p → Set.BijOn e.symm.toMonoidHom {y | y ^ n = 1} {y | y ^ n = 1} := by
      intro n _ _
      refine ⟨fun y hy => ?_, e.symm.injective.injOn, fun y hy => ⟨e y, ?_, e.symm_apply_apply y⟩⟩
      · show (e.symm y) ^ n = 1
        rw [← map_pow, show y ^ n = 1 from hy, map_one]
      · show (e y) ^ n = 1
        rw [← map_pow, show y ^ n = 1 from hy, map_one]
    have hisom : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a a', Out.WeilIs ((Over.pullback f).obj o.A)
        ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) (n : ℤ)
        (e.symm.toMonoidHom (I.ev n a)) (e.symm.toMonoidHom (I.ev n a')) (unitOn (I.ζ n ^ (2 * D.EF a a'))) := by
      intro n h1 h2 a a'
      exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _)
        (pull_isLB (pull_isLB o.isLB _) _) h
        (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _))) (Over.mk x) n _ _
        (I.ev n a) (I.ev n a') _ (hsymm _).symm (hsymm _).symm).2 (I.isom n h1 h2 a a')
    obtain ⟨I', hI'⟩ := tate_transport (Q' := Over.mk x ⟶ (Over.pullback f).obj o.A) (act' := fun c g => g ≫ (actPull f o.act).act c)
      (e' := fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
        ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z))
      I e.symm.toMonoidHom hact hbij hisom
    refine ⟨I', fun y => ?_⟩
    rw [hI']
    refine (MulEquiv.eq_symm_apply e).2 ?_
    refine Eq.trans (Over.OverMorphism.ext ?_) ((GlobalTheory.SiegelPull.push_secPull h (o.eta y) (Over.mk x)).trans (hI y))
    rw [he]
    rfl

def objPull (o : Obj b N s) (f : S' ⟶ S) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') : Obj b N s' where
  A := (Over.pullback f).obj o.A
  ab :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  act := actPull f o.act
  P := o.P.pull (pφ₂ f o.A)
  isLB := pull_isLB o.isLB (pφ₂ f o.A)
  rig₁ := by
    obtain ⟨t₁, ht₁⟩ := o.rig₁
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      (fun _ => Pdiv.PullbackComparison.lift_one_id f o.A)) t₁ ht₁
  rig₂ := by
    obtain ⟨t₂, ht₂⟩ := o.rig₂
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      (fun _ => Pdiv.PullbackComparison.lift_id_one f o.A)) t₂ ht₂
  symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) (fun _ => Pdiv.PullbackComparison.lift_swap f o.A)) o.symm
  ample := (GlobalTheory.pol_pull S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) o.ab
    (isGrpPullback f o.A) (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _)))).2.1 o.ample
  kerP := by
    obtain ⟨e, he, H⟩ := o.kerP
    refine ⟨e, he, fun T x hx => ?_⟩
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) T ?_
    rw [map_pow, map_one]
    exact H _ _ (gen_push f (isGrpPullback f o.A) (isSquare f o.A) o.isLB (pull_isLB o.isLB _)
      (gen_refl _ (pull_isLB o.isLB _)) T x hx)
  rosati c := LBIso.chartPull
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) (fun _ => lift_pφ₂ f o.A _ _ _ _
        (by rw [Over.comp_left, Over.comp_left, Category.assoc, actPull_left, ← Category.assoc, ← pφ₂_fst,
          Category.assoc])
        (pφ₂_snd f o.A).symm))
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) (fun _ => lift_pφ₂ f o.A _ _ _ _
        (pφ₂_fst f o.A).symm
        (by rw [Over.comp_left, Over.comp_left, Category.assoc, actPull_left, ← Category.assoc, ← pφ₂_snd,
          Category.assoc])))
      (o.rosati c)
  lie R' _ β x hx v hv := by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback f o.A) (epsPtR x)
      (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f) (Category.assoc _ _ _).symm
    obtain ⟨w, hw, hv'⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hs, hx]) (e v)
      ((isTanScal_pull f o.act x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_pull f o.act x e he _ _ _).2
      (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
    rw [hv', map_list_prod, List.map_ofFn]
    congr 1
    exact congrArg List.ofFn (funext fun i => (e.apply_symm_apply (w i)).symm)
  lieRank k _ _ x β hx i :=
    (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A _ f (pφ f o.A) (o.act.toF D) ((actPull f o.act).toF D)
      (isGrpPullback f o.A) (fun c => actPull_left f o.act _) k x _ D.m).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hs, hx]) i)
  eta y := GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y)
  eta_add y y' := GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ (by
    rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', o.eta_add,
      MonObj.comp_mul])
  eta_lin c y := GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ (by
    rw [GlobalTheory.SiegelPull.push_secPull', o.eta_lin, push_act, GlobalTheory.SiegelPull.push_secPull', Category.assoc])
  eta_ker y := GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ (by
    rw [map_one, GlobalTheory.SiegelPull.push_secPull', o.eta_ker, MonObj.comp_one])
  geom k _ _ x β hx := geom_pull o f s' hs k x β hx

def objPullMap (o : Obj b N s) (f : S' ⟶ S) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') : ObjMap (objPull o f s' hs) o f where
  φ := pφ f o.A
  φ₂ := pφ₂ f o.A
  cart := isGrpPullback f o.A
  sq := isSquare f o.A
  act c := actPull_left f o.act c
  pol := gen_refl _ (pull_isLB o.isLB _)
  eta y := GlobalTheory.SiegelPull.secPull_left (isGrpPullback f o.A) _

end GlobalTheory.HTPullEvery

theorem GlobalTheory.HTPullEvery.exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ o : Obj b N s, ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ f hs o => ⟨_, ⟨GlobalTheory.HTPullEvery.objPullMap o f _ hs⟩⟩
