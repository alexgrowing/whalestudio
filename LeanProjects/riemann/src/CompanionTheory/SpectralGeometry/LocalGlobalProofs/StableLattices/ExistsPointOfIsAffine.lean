import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.LineBundleSpreadsOut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualAb

section Unique

variable {S : Scheme.{0}} {A B T : Over S} [GrpObj B]

theorem point_ext {P : LB (A ⊗ B).left} (hP : P.IsLB) (a₂ : IsAdditive (swap P)) (r : RightZero A B P)
    {x x' : T ⟶ B} (e : evc hP (fst A T) (snd A T ≫ x) = evc hP (fst A T) (snd A T ≫ x')) : x = x' := by
  have e₁ := (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂ _ (fst A T) (snd A T ≫ (x * x'⁻¹)) (snd A T ≫ x')
  rw [← MonObj.comp_mul, inv_mul_cancel_right, e] at e₁
  exact mul_inv_eq_one.1 (r T _ ((triv_ev_iff hP _ _).2 (right_eq_add.1 e₁)))

end Unique

section Level

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem exists_level [IsNoetherianRing R] (hA : IsAbelianScheme A) {C : Type} [CommRing C] (t : Sp C ⟶ Sp R)
    {M : LB (A ⊗ Over.mk t).left} (hM : M.IsLB) :
    ∃ (D : Type) (_ : CommRing D) (i : D →+* C) (tD : Sp D ⟶ Sp R) (N : LB (A ⊗ Over.mk tD).left)
      (hN : N.IsLB) (w : spMap i ≫ tD = t), IsNoetherianRing D ∧
      cls M hM = evc hN (fst A _) (snd A _ ≫ (Over.homMk (spMap i) w : Over.mk t ⟶ Over.mk tD)) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : R →+* C, spMap ψ = t := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  letI := ψ.toAlgebra
  haveI := hA.proper
  have H : IsPullback (fst A (Over.mk (spMap ψ))).left (snd A (Over.mk (spMap ψ))).left A.hom
      (spMap (algebraMap R C)) := IsPullback.of_hasPullback _ _
  obtain ⟨D, hD, N, hN, h⟩ := GlobalTheory.CompanionTheory.Ar.Approx.lb_descends_fg R C A.left _ A.hom _ _ inferInstance inferInstance H M hM
  have w : spMap D.val.toRingHom ≫ spMap (algebraMap R D) = spMap ψ := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  haveI : Algebra.FiniteType R D := (Subalgebra.fg_iff_finiteType D).1 hD
  refine ⟨D, inferInstance, D.val.toRingHom, spMap (algebraMap R D), N, hN, w,
    Algebra.FiniteType.isNoetherianRing R D, ?_⟩
  refine (cls_eq_iff hM (pull_isLB hN _)).2 (h _ ?_ ?_)
  · exact lift_left_fst _ _
  · exact lift_left_snd _ _ |>.trans rfl

end Level

section Universal

variable {S : Scheme.{0}} {A T₀ Y : Over S} [GrpObj A]

abbrev uniE (N : LB (A ⊗ T₀).left) : LB (A ⊗ (A ⊗ T₀)).left :=
  ev N (fst A (A ⊗ T₀) * (snd A (A ⊗ T₀) ≫ fst A T₀)) (snd A (A ⊗ T₀) ≫ snd A T₀)

abbrev uniF (N : LB (A ⊗ T₀).left) : LB (A ⊗ (A ⊗ T₀)).left :=
  tens (ev N (fst A (A ⊗ T₀)) (snd A (A ⊗ T₀) ≫ snd A T₀))
    (ev N (snd A (A ⊗ T₀) ≫ fst A T₀) (snd A (A ⊗ T₀) ≫ snd A T₀))

theorem lbIso_uni_iff {N : LB (A ⊗ T₀).left} (hN : N.IsLB) (y : Y ⟶ A ⊗ (A ⊗ T₀)) :
    LBIso ((uniE N).pull y.left) ((uniF N).pull y.left) ↔
      evc hN ((y ≫ fst A _) * (y ≫ snd A _ ≫ fst A T₀)) (y ≫ snd A _ ≫ snd A T₀) =
        evc hN (y ≫ fst A _) (y ≫ snd A _ ≫ snd A T₀) +
          evc hN (y ≫ snd A _ ≫ fst A T₀) (y ≫ snd A _ ≫ snd A T₀) := by
  have hE : (uniE N).IsLB := pull_isLB hN _
  have h₁ := pull_isLB hN (lift (fst A (A ⊗ T₀)) (snd A (A ⊗ T₀) ≫ snd A T₀)).left
  have h₂ := pull_isLB hN (lift (snd A (A ⊗ T₀) ≫ fst A T₀) (snd A (A ⊗ T₀) ≫ snd A T₀)).left
  have hF : (uniF N).IsLB := isLB_tens h₁ h₂
  rw [← cls_eq_iff (pull_isLB hE _) (pull_isLB hF _), cls_pull hE, cls_pull hF, cls_tens h₁ h₂, cls_ev hN, cls_ev hN,
    cls_ev hN, map_add, pull_evc, pull_evc, pull_evc, MonObj.comp_mul]

end Universal

section Spread

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem exists_additive_level (hA : IsAbelianScheme A) {C D : Type} [CommRing C] [CommRing D] [IsNoetherianRing D]
    (i : D →+* C) (tD : Sp D ⟶ Sp R) {M : LB (A ⊗ Over.mk (spMap i ≫ tD)).left} (hM : M.IsLB) (hadd : IsAdditive M)
    {N : LB (A ⊗ Over.mk tD).left} (hN : N.IsLB)
    (e : cls M hM = evc hN (fst A _)
      (snd A _ ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ tD) ⟶ Over.mk tD))) :
    ∃ (D₁ : Type) (_ : CommRing D₁) (j : D →+* D₁) (i₁ : D₁ →+* C), IsNoetherianRing D₁ ∧ i₁.comp j = i ∧
      IsAdditive (ev N (fst A (Over.mk (spMap j ≫ tD)))
        (snd A _ ≫ (Over.homMk (spMap j) rfl : Over.mk (spMap j ≫ tD) ⟶ Over.mk tD))) := by
  letI := i.toAlgebra
  haveI := hA.proper
  let T₀ : Over (Sp R) := Over.mk tD
  let u : Over.mk (spMap i ≫ tD) ⟶ T₀ := Over.homMk (spMap i) rfl
  let τ : A ⊗ (A ⊗ T₀) ⟶ T₀ := snd A _ ≫ snd A T₀
  let pB : (A ⊗ (A ⊗ T₀)).left ⟶ Sp D := τ.left
  have q₁ : ∀ T : Over (Sp R), QuasiCompact (snd A T).left := fun T ↦
    inferInstanceAs (QuasiCompact (pullback.snd A.hom T.hom))
  have q₂ : ∀ T : Over (Sp R), QuasiSeparated (snd A T).left := fun T ↦
    inferInstanceAs (QuasiSeparated (pullback.snd A.hom T.hom))
  haveI : QuasiCompact pB := by
    have := q₁ T₀
    have := q₁ (A ⊗ T₀)
    exact inferInstanceAs (QuasiCompact ((snd A (A ⊗ T₀)).left ≫ (snd A T₀).left))
  haveI : QuasiSeparated pB := by
    have := q₂ T₀
    have := q₂ (A ⊗ T₀)
    exact inferInstanceAs (QuasiSeparated ((snd A (A ⊗ T₀)).left ≫ (snd A T₀).left))
  have hE : (uniE N).IsLB := pull_isLB hN _
  have hF : (uniF N).IsLB := isLB_tens (pull_isLB hN _) (pull_isLB hN _)
  let fC := pullback.fst pB (spMap (algebraMap D C))
  let c : Over.mk (fC ≫ (A ⊗ (A ⊗ T₀)).hom) ⟶ A ⊗ (A ⊗ T₀) := Over.homMk fC rfl
  have wτ : pB ≫ tD = (A ⊗ (A ⊗ T₀)).hom := Over.w τ
  let τc : Over.mk (fC ≫ (A ⊗ (A ⊗ T₀)).hom) ⟶ Over.mk (spMap i ≫ tD) :=
    Over.homMk (pullback.snd pB _) (by
      show pullback.snd pB (spMap (algebraMap D C)) ≫ spMap i ≫ tD = fC ≫ (A ⊗ (A ⊗ T₀)).hom
      rw [← wτ, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ tD) (pullback.condition (f := pB) (g := spMap (algebraMap D C))).symm)
  have hc : c ≫ τ = τc ≫ u := Over.OverMorphism.ext (pullback.condition (f := pB) (g := spMap (algebraMap D C)))
  have H := (lbIso_uni_iff hN c).2 (by
    have hc' : c ≫ snd A _ ≫ snd A T₀ = τc ≫ u := hc
    rw [hc', ← GlobalTheory.BirigidLift.evc_of_cls hN hM e, ← GlobalTheory.BirigidLift.evc_of_cls hN hM e,
      ← GlobalTheory.BirigidLift.evc_of_cls hN hM e]
    exact (isAdditive_iff hM).1 hadd _ _ _ _)
  obtain ⟨s, H₁⟩ := GlobalTheory.exists_finset_lbIso_adjoin pB _ _ hE hF H
  let D₁ := Algebra.adjoin D (s : Set C)
  let j : D →+* D₁ := algebraMap D D₁
  haveI : Algebra.FiniteType D D₁ := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  refine ⟨D₁, inferInstance, j, D₁.val.toRingHom, Algebra.FiniteType.isNoetherianRing D _,
    RingHom.ext fun x ↦ rfl, ?_⟩
  let f₁ := pullback.fst pB (spMap (algebraMap D D₁))
  let c₁ : Over.mk (f₁ ≫ (A ⊗ (A ⊗ T₀)).hom) ⟶ A ⊗ (A ⊗ T₀) := Over.homMk f₁ rfl
  have K := (lbIso_uni_iff hN c₁).1 H₁
  let v : Over.mk (spMap j ≫ tD) ⟶ T₀ := Over.homMk (spMap j) rfl
  have hN₁ : (ev N (fst A (Over.mk (spMap j ≫ tD))) (snd A _ ≫ v)).IsLB := pull_isLB hN _
  refine (isAdditive_iff hN₁).2 fun Y a a' t ↦ ?_
  rw [GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl, GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl,
    GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl]
  obtain ⟨y, hy⟩ : ∃ y : Y ⟶ A ⊗ (A ⊗ T₀), y = lift a (lift a' (t ≫ v)) := ⟨_, rfl⟩
  have y₁ : y ≫ fst A _ = a := by rw [hy, lift_fst]
  have y₂ : y ≫ snd A _ ≫ fst A T₀ = a' := by rw [hy, lift_snd_assoc, lift_fst]
  have y₃ : y ≫ snd A _ ≫ snd A T₀ = t ≫ v := by rw [hy, lift_snd_assoc, lift_snd]
  have w : y.left ≫ pB = t.left ≫ spMap (algebraMap D D₁) := congrArg (fun q ↦ q.left) y₃
  let g : Y ⟶ Over.mk (f₁ ≫ (A ⊗ (A ⊗ T₀)).hom) := Over.homMk (pullback.lift y.left t.left w) (by
    show pullback.lift y.left t.left w ≫ f₁ ≫ (A ⊗ (A ⊗ T₀)).hom = Y.hom
    rw [pullback.lift_fst_assoc]
    exact Over.w y)
  have hg : g ≫ c₁ = y := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have K' := congrArg (CechPic.pull g.left) K
  rw [map_add, pull_evc, pull_evc, pull_evc, MonObj.comp_mul, ← Category.assoc g, ← Category.assoc g,
    ← Category.assoc g, hg, y₁, y₂, y₃] at K'
  exact K'

end Spread

section Affine

variable {R : Type} [CommRing R] [IsNoetherianRing R] {A B : Over (Sp R)} [GrpObj A]

theorem exists_point_spec (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (U : UnivNoeth A B P)
    {C : Type} [CommRing C] (t : Sp C ⟶ Sp R) {M : LB (A ⊗ Over.mk t).left} (hM : M.IsLB) (hadd : IsAdditive M) :
    ∃ x : Over.mk t ⟶ B, cls M hM = evc hP (fst A _) (snd A _ ≫ x) := by
  obtain ⟨D, _, i, tD, N, hN, rfl, _, e⟩ := exists_level hA t hM
  obtain ⟨D₁, _, j, i₁, _, rfl, ha⟩ := exists_additive_level hA i tD hM hadd hN e
  have hN₁ := pull_isLB hN (lift (fst A (Over.mk (spMap j ≫ tD)))
    (snd A _ ≫ (Over.homMk (spMap j) rfl : Over.mk (spMap j ≫ tD) ⟶ Over.mk tD))).left
  obtain ⟨x₁, hx₁⟩ := U D₁ (spMap j ≫ tD) _ hN₁ ha
  have hcomp : spMap (i₁.comp j) = spMap i₁ ≫ spMap j := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let v : Over.mk (spMap j ≫ tD) ⟶ Over.mk tD := Over.homMk (spMap j) rfl
  let u₁ : Over.mk (spMap (i₁.comp j) ≫ tD) ⟶ Over.mk (spMap j ≫ tD) := Over.homMk (spMap i₁) (by
    show spMap i₁ ≫ spMap j ≫ tD = spMap (i₁.comp j) ≫ tD
    rw [hcomp, Category.assoc])
  have hv : (Over.homMk (spMap (i₁.comp j)) rfl : Over.mk (spMap (i₁.comp j) ≫ tD) ⟶ Over.mk tD) = u₁ ≫ v :=
    Over.OverMorphism.ext hcomp
  refine ⟨u₁ ≫ x₁, ?_⟩
  rw [e, hv, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl,
    GlobalTheory.BirigidLift.evc_of_cls hP hN₁ ((cls_eq_iff hN₁ (pull_isLB hP _)).2 hx₁), Category.assoc]

end Affine

section Pull

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A]

theorem cls_eq_evc {M : LB (A ⊗ T).left} (hM : M.IsLB) : cls M hM = evc hM (fst A T) (snd A T) := by
  rw [evc, lift_fst_snd, Over.id_left, pull_id]

theorem isAdditive_ev {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (v : T' ⟶ T) :
    IsAdditive (ev M (fst A T') (snd A T' ≫ v)) := by
  have hN : (ev M (fst A T') (snd A T' ≫ v)).IsLB := pull_isLB hM _
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  rw [GlobalTheory.BirigidLift.evc_of_cls hM hN rfl, GlobalTheory.BirigidLift.evc_of_cls hM hN rfl,
    GlobalTheory.BirigidLift.evc_of_cls hM hN rfl]
  exact (isAdditive_iff hM).1 h _ _ _ _

theorem surjective_snd (hA : IsAbelianScheme A) (V : T.left.Opens) :
    Function.Surjective ((snd A T).left ∣_ V).appTop.hom := by
  have hG := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A T.hom)
  have hV := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG (isGrpPullback_pullback _ V.ι)
  have h1 : Function.Surjective (pullback.snd (pullback.snd A.hom T.hom) V.ι).appTop.hom :=
    (GlobalTheory.globalFns_holds _ _ hV).2
  have e : (snd A T).left ∣_ V =
      (pullbackRestrictIsoRestrict (pullback.snd A.hom T.hom) V).inv ≫ pullback.snd (pullback.snd A.hom T.hom) V.ι := rfl
  have h2 := (ConcreteCategory.bijective_of_isIso
    ((pullbackRestrictIsoRestrict (pullback.snd A.hom T.hom) V).inv.app ⊤)).2.comp h1
  rw [e, Scheme.Hom.comp_appTop]
  exact h2

end Pull

section Global

variable {R : Type} [CommRing R] [IsNoetherianRing R] {A B : Over (Sp R)} [GrpObj A]

theorem exists_point_of_isAffine (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (U : UnivNoeth A B P) {T : Over (Sp R)} [IsAffine T.left] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (hadd : IsAdditive M) : ∃ x : T ⟶ B, cls M hM = evc hP (fst A T) (snd A T ≫ x) := by
  let e := T.left.isoSpec
  let t : Sp Γ(T.left, ⊤) ⟶ Sp R := e.inv ≫ T.hom
  let i : Over.mk t ⟶ T := Over.homMk e.inv rfl
  let i' : T ⟶ Over.mk t := Over.homMk e.hom (by
    show e.hom ≫ e.inv ≫ T.hom = T.hom
    rw [e.hom_inv_id_assoc])
  have hii : i' ≫ i = 𝟙 T := Over.OverMorphism.ext e.hom_inv_id
  have hN : (ev M (fst A (Over.mk t)) (snd A _ ≫ i)).IsLB := pull_isLB hM _
  obtain ⟨x, hx⟩ := exists_point_spec hA hP U t hN (isAdditive_ev hM hadd i)
  refine ⟨i' ≫ x, ?_⟩
  have k := GlobalTheory.BirigidLift.evc_of_cls hP hN hx (fst A T) (snd A T ≫ i')
  rw [GlobalTheory.BirigidLift.evc_of_cls hM hN rfl, Category.assoc, Category.assoc, hii, Category.comp_id] at k
  rw [cls_eq_evc hM]
  exact k

end Global

section Glue

variable {R : Type} [CommRing R] [IsNoetherianRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem exists_point (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (a₁ : IsAdditive P)
    (a₂ : IsAdditive (swap P)) (r : RightZero A B P) (U : UnivNoeth A B P) {T : Over (Sp R)}
    {M : LB (A ⊗ T).left} (hM : M.IsLB) (hadd : IsAdditive M) :
    ∃ x : T ⟶ B, cls M hM = evc hP (fst A T) (snd A T ≫ x) := by
  let 𝒰 := T.left.affineCover
  let Ti : ∀ i, Over (Sp R) := fun i ↦ Over.mk (𝒰.f i ≫ T.hom)
  let j : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (𝒰.f i) rfl
  have hN : ∀ i, (ev M (fst A (Ti i)) (snd A _ ≫ j i)).IsLB := fun i ↦ pull_isLB hM _
  have loc : ∀ i, ∃ x : Ti i ⟶ B, cls _ (hN i) = evc hP (fst A _) (snd A _ ≫ x) := fun i ↦ by
    haveI : IsAffine (Ti i).left := inferInstanceAs (IsAffine (𝒰.X i))
    exact exists_point_of_isAffine hA hP U (hN i) (isAdditive_ev hM hadd _)
  choose x hx using loc
  have val : ∀ i {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ Ti i), evc hM a (t ≫ j i) = evc hP a (t ≫ x i) :=
    fun i Y a t ↦ (GlobalTheory.BirigidLift.evc_of_cls hM (hN i) rfl a t).symm.trans
      (GlobalTheory.BirigidLift.evc_of_cls hP (hN i) (hx i) a t)
  have ov : ∀ i i', pullback.fst (𝒰.f i) (𝒰.f i') ≫ (x i).left = pullback.snd (𝒰.f i) (𝒰.f i') ≫ (x i').left := by
    intro i i'
    let W : Over (Sp R) := Over.mk (pullback.fst (𝒰.f i) (𝒰.f i') ≫ 𝒰.f i ≫ T.hom)
    let a : W ⟶ Ti i := Over.homMk (pullback.fst _ _) rfl
    let b : W ⟶ Ti i' := Over.homMk (pullback.snd _ _) (by
      show pullback.snd (𝒰.f i) (𝒰.f i') ≫ 𝒰.f i' ≫ T.hom = pullback.fst (𝒰.f i) (𝒰.f i') ≫ 𝒰.f i ≫ T.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc])
    have hab : a ≫ j i = b ≫ j i' := Over.OverMorphism.ext pullback.condition
    have e := point_ext hP a₂ r (x := a ≫ x i) (x' := b ≫ x i') (by
      rw [← Category.assoc, ← Category.assoc, ← val, ← val, Category.assoc, Category.assoc, hab])
    exact congrArg (fun q ↦ q.left) e
  let x₀ : T.left ⟶ B.left := 𝒰.glueMorphisms (fun i ↦ (x i).left) ov
  have hx₀ : ∀ i, 𝒰.f i ≫ x₀ = (x i).left := fun i ↦ 𝒰.ι_glueMorphisms _ ov i
  let X : T ⟶ B := Over.homMk x₀ (𝒰.hom_ext _ _ fun i ↦ by
    show 𝒰.f i ≫ x₀ ≫ B.hom = 𝒰.f i ≫ T.hom
    rw [reassoc_of% hx₀ i]
    exact Over.w (x i))
  have hX : ∀ i, j i ≫ X = x i := fun i ↦ Over.OverMorphism.ext (hx₀ i)
  refine ⟨X, ?_⟩
  obtain ⟨L, hL, hd⟩ := cls_surj (cls M hM - evc hP (fst A T) (snd A T ≫ X))
  have h0 : Triv L := by
    refine GlobalTheory.CubeGlue.triv_of_locally_triv hL (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left
      ((lift_left_snd _ _).trans (Over.id_left _)) (surjective_snd hA) ?_ ?_
    · refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
      rw [cls_pull hL, hd, map_sub, cls_eq_evc hM, pull_evc, pull_evc, lift_fst,
        lift_snd_assoc, lift_snd, hadd.evc_one hM, a₁.evc_one hP, sub_zero]
    · intro z
      let i := 𝒰.idx z
      let V := (𝒰.f i).opensRange
      refine ⟨V, 𝒰.covers z, ?_⟩
      let W := (snd A T).left ⁻¹ᵁ V
      have hl : Set.range (W.ι ≫ (snd A T).left) ⊆ Set.range (𝒰.f i) := by
        rintro _ ⟨y, rfl⟩
        exact y.2
      let l := IsOpenImmersion.lift (𝒰.f i) (W.ι ≫ (snd A T).left) hl
      have hfac : l ≫ 𝒰.f i = W.ι ≫ (snd A T).left := IsOpenImmersion.lift_fac _ _ _
      let Wo : Over (Sp R) := Over.mk (W.ι ≫ (A ⊗ T).hom)
      let w : Wo ⟶ A ⊗ T := Over.homMk W.ι rfl
      let t₀ : Wo ⟶ Ti i := Over.homMk l (by
        show l ≫ 𝒰.f i ≫ T.hom = W.ι ≫ (A ⊗ T).hom
        rw [← Category.assoc, hfac, Category.assoc]
        exact congrArg (W.ι ≫ ·) (Over.w (snd A T)))
      have ht : t₀ ≫ j i = w ≫ snd A T := Over.OverMorphism.ext hfac
      refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
      rw [cls_pull hL, hd]
      show CechPic.pull w.left _ = 0
      rw [map_sub, cls_eq_evc hM, pull_evc, pull_evc, ← Category.assoc w, ← ht, Category.assoc, hX, val, sub_self]
  rw [← sub_eq_zero, ← hd]
  exact (cls_eq_zero_iff hL).2 h0

end Glue

theorem finDual_of_univNoeth : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, PreDual A B P → UnivNoeth A B P) → FinDual := by
  intro H R _ _ A B _ _ g hA hB gA gB P hD
  have U := H R A B g hA hB gA gB P hD
  refine ⟨hD.isLB, hD.add₁, GlobalTheory.BirigidLift.triv_right hD.isLB hD.add₂, fun T M hM ha ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_point hA hD.isLB hD.add₁ hD.add₂ hD.right U hM ha
  refine ⟨x, (cls_eq_iff hM (pull_isLB hD.isLB _)).1 hx, fun y hy ↦ ?_⟩
  exact point_ext hD.isLB hD.add₂ hD.right (((cls_eq_iff hM (pull_isLB hD.isLB _)).2 hy).symm.trans hx)

end GlobalTheory.CompanionTheory.DualAb
