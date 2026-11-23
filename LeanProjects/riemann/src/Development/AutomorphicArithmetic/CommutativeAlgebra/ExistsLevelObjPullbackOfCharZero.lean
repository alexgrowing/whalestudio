import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.LevDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

noncomputable section

namespace UpperTheory.LevPull

open GlobalTheory.PELU
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (pφ pφ₂ isSquare pφ₂_fst pφ₂_snd isGrpPullback gen_refl)
open GlobalTheory.HTPullEvery (lift_pφ₂ map_left_pφ push_map)

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

private def pullAct (a : OActN O A) : OActN O ((Over.pullback f).obj A) where
  act c := (Over.pullback f).map (a.act c)
  hom c := by have := a.hom c; infer_instance
  one := by simp [a.one]
  mul b c := by simp [a.mul]
  add b c := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f A) _ ?_
    rw [map_mul]
    simp only [push_map, a.add, MonObj.comp_mul]

private theorem pullAct_sq (a : OActN O A) (c : O) :
    ((pullAct f a).act c).left ≫ pφ f A = pφ f A ≫ (a.act c).left :=
  map_left_pφ f A (a.act c)

private theorem push_pullAct (a : OActN O A) {T : Over S'} (u : T ⟶ (Over.pullback f).obj A) (c : O) :
    pushHom (isGrpPullback f A) T (u ≫ (pullAct f a).act c) = pushHom (isGrpPullback f A) T u ≫ a.act c := by
  apply Over.OverMorphism.ext
  change (u ≫ (pullAct f a).act c).left ≫ pφ f A = (u.left ≫ pφ f A) ≫ (a.act c).left
  simp [pullAct_sq]

end Act

section Tan

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

private theorem tanScal_iff (a : OActN O A) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ (Over.pullback f).obj A) ≃* (epsPtR (x ≫ f) ⟶ A))
    (he : ∀ v, (e v).left = v.left ≫ pφ f A) (c : O) (r : R') (v : epsPtR x ⟶ (Over.pullback f).obj A) :
    IsTanScal (pullAct f a) x c r v ↔ IsTanScal a (x ≫ f) c r (e v) := by
  have cart := isGrpPullback f A
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv cart (Over.mk x) (x ≫ f) rfl
  have unit : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ pφ f A := by
    rw [← he₀, map_one]
  have retr : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have scale : spMap (epsScaleR r) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have down : e (v ≫ (pullAct f a).act c) = e v ≫ a.act c := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he, Category.assoc, pullAct_sq]
  have wv : v.left ≫ ((Over.pullback f).obj A).hom = spMap (algebraMap R' (DualNumber R')) ≫ x := Over.w v
  have wc : (v ≫ (pullAct f a).act c).left ≫ ((Over.pullback f).obj A).hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x := Over.w _
  have w1 : (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ ((Over.pullback f).obj A).hom = x := Over.w _
  unfold IsTanScal
  rw [← down, he, he, unit]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [← Category.assoc, h₁], by rw [h₂, Category.assoc]⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨cart.1.hom_ext (by simpa using h₁) ?_, cart.1.hom_ext (by simpa using h₂) ?_⟩
    · rw [Category.assoc, wv, w1, ← Category.assoc, retr, Category.id_comp]
    · rw [wc, Category.assoc, wv, ← Category.assoc, scale]

end Tan

section Tate

variable {G : GDatum}

private theorem tate_along {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : G.O → Q → Q} {act' : G.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (I : GTateIso G k Q act e) (r : Q ≃* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hisom : ∀ n, 0 < n → ∀ x y, e' n (r (I.ev n x)) (r (I.ev n y)) (I.ζ n ^ (2 * G.EF x y))) :
    ∃ I' : GTateIso G k Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) :=
  ⟨{ ζ := I.ζ
     ζ_prim := I.ζ_prim
     ζ_pow := I.ζ_pow
     ev := fun n x => r (I.ev n x)
     add := fun n x y => by rw [I.add, map_mul]
     lin := fun n c x => by rw [I.lin, hact]
     ker := fun n hn x => by rw [map_eq_one_iff r r.injective, I.ker n hn]
     onto := fun n hn q => by
       have : q ^ n = 1 ↔ (r.symm q) ^ n = 1 := by
         rw [← map_pow, map_eq_one_iff r.symm r.symm.injective]
       rw [this, I.onto n hn]
       exact exists_congr fun x => by rw [MulEquiv.eq_symm_apply]
     tower := fun n m hn hm x => by rw [← map_pow, I.tower n m hn hm]
     isom := hisom }, fun _ _ => rfl⟩

end Tate

section Obj

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R}
  {N : ℕ} {s : S ⟶ Sp R}

private theorem geom_of_pull (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S') (β : R →+* k) (hx : x ≫ s' = spMap β) :
    ∃ I : GTateIso G k (Over.mk x ⟶ (Over.pullback f).obj o.A) (fun c g => g ≫ (pullAct f o.act).act c)
        (fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
          ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y) = I.ev N y := by
  have cart := isGrpPullback f o.A
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv cart (Over.mk x) (x ≫ f) rfl
  obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hs, hx])
  have back : ∀ q, (e.symm q).left ≫ pφ f o.A = q.left := fun q => by rw [← he, e.apply_symm_apply]
  have hact : ∀ c q, e.symm (q ≫ o.act.act c) = e.symm q ≫ (pullAct f o.act).act c := by
    intro c q
    rw [MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, pullAct_sq, ← Category.assoc, back]
  have hisom : ∀ n : ℕ, 0 < n → ∀ a a', Out.WeilIs ((Over.pullback f).obj o.A)
      ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) (n : ℤ)
      (e.symm (I.ev n a)) (e.symm (I.ev n a')) (unitOn (I.ζ n ^ (2 * G.EF a a'))) := fun n hn a a' =>
    (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _)
      (pull_isLB (pull_isLB o.isLB _) _) cart
      (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _))) (Over.mk x) n _ _
      (I.ev n a) (I.ev n a') _ (back _).symm (back _).symm).2 (I.isom n hn a a')
  obtain ⟨I', hI'⟩ := tate_along (Q' := Over.mk x ⟶ (Over.pullback f).obj o.A)
    (act' := fun c g => g ≫ (pullAct f o.act).act c)
    (e' := fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
      ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z))
    I e.symm hact hisom
  refine ⟨I', fun y => ?_⟩
  rw [hI', MulEquiv.eq_symm_apply, ← hI y]
  refine Eq.trans ?_ (GlobalTheory.SiegelPull.push_secPull cart (o.eta y) (Over.mk x))
  apply Over.OverMorphism.ext
  rw [he]
  rfl

private def baseChange (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') : GObj gb N s' where
  A := (Over.pullback f).obj o.A
  ab :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  act := pullAct f o.act
  P := o.P.pull (pφ₂ f o.A)
  isLB := pull_isLB o.isLB (pφ₂ f o.A)
  rig₁ := by
    obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      fun _ => Pdiv.PullbackComparison.lift_one_id f o.A) t ht
  rig₂ := by
    obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      fun _ => Pdiv.PullbackComparison.lift_id_one f o.A) t ht
  symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
    (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ => Pdiv.PullbackComparison.lift_swap f o.A) o.symm
  ample := (GlobalTheory.pol_pull S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) o.ab
    (isGrpPullback f o.A) (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _)))).2.1 o.ample
  rosati c := by
    have h₁ : (fst ((Over.pullback f).obj o.A) _ ≫ (pullAct f o.act).act c).left ≫ pφ f o.A =
        pφ₂ f o.A ≫ (fst o.A o.A ≫ o.act.act c).left := by
      simp only [Over.comp_left, Category.assoc, pullAct_sq]
      rw [← Category.assoc, ← pφ₂_fst, Category.assoc]
    have h₂ : (snd ((Over.pullback f).obj o.A) _ ≫ (pullAct f o.act).act (G.star c).unop).left ≫ pφ f o.A =
        pφ₂ f o.A ≫ (snd o.A o.A ≫ o.act.act (G.star c).unop).left := by
      simp only [Over.comp_left, Category.assoc, pullAct_sq]
      rw [← Category.assoc, ← pφ₂_snd, Category.assoc]
    exact LBIso.chartPull
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ =>
        lift_pφ₂ f o.A _ _ _ _ h₁ (pφ₂_snd f o.A).symm)
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ =>
        lift_pφ₂ f o.A _ _ _ _ (pφ₂_fst f o.A).symm h₂)
      (o.rosati c)
  lie R' _ β x hx v hv := by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback f o.A) (epsPtR x)
      (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f) (Category.assoc _ _ _).symm
    obtain ⟨w, hw, hsum⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hs, hx]) (e v)
      ((tanScal_iff f o.act x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => ?_, ?_⟩
    · rw [tanScal_iff f o.act x e he, e.apply_symm_apply]
      exact hw i c
    · rw [← e.symm_apply_apply v, hsum, map_list_prod, List.map_ofFn]
      rfl
  lieRank k _ _ x β hx i :=
    (GlobalTheory.LiePull.lieMult_pull (𝓞 G.F) S S' o.A _ f (pφ f o.A) (actF o.act) (actF (pullAct f o.act))
      (isGrpPullback f o.A) (fun c => pullAct_sq f o.act _) k x _ G.m).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hs, hx]) i)
  eta y := GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y)
  eta_add y y' := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [map_mul, GlobalTheory.SiegelPull.push_secPull', o.eta_add, MonObj.comp_mul]
  eta_lin c y := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [push_pullAct, GlobalTheory.SiegelPull.push_secPull', o.eta_lin, Category.assoc]
  eta_ker y := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [map_one, GlobalTheory.SiegelPull.push_secPull', o.eta_ker, MonObj.comp_one]
  geom k _ _ x β hx := geom_of_pull f o s' hs k x β hx

private def baseChangeMap (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') :
    GObjMap (baseChange f o s' hs) o f where
  φ := pφ f o.A
  φ₂ := pφ₂ f o.A
  cart := isGrpPullback f o.A
  sq := isSquare f o.A
  act c := pullAct_sq f o.act c
  pol := gen_refl _ (pull_isLB o.isLB _)
  eta y := GlobalTheory.SiegelPull.secPull_left (isGrpPullback f o.A) _

end Obj

end UpperTheory.LevPull

theorem UpperTheory.exists_levelObj_pullback_of_charZero :
    ∀ {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R}
        (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ o : GObj gb N s, ∃ o' : GObj gb N s', Nonempty (GObjMap o' o f) :=
  fun s' f hs o => ⟨_, ⟨UpperTheory.LevPull.baseChangeMap f o s' hs⟩⟩
