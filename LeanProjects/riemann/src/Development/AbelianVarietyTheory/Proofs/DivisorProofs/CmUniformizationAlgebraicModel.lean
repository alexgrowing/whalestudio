import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyPeriodNormalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismDescendsToAlgebraicModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

section ModelOver

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift

namespace GlobalTheory.CMModel

theorem exists_obj_of_isGrpPullback_over (HD : GlobalTheory.Published.DualAbelianScheme) {F : Type} [Field F] [NumberField F]
    {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (c₀ : 𝔠.elt) (hc₀ : IsTotPos (c₀ : F)) (A₀ : Over (Sp Qb)) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p) {S₀ : Scheme.{0}} (G₀ : Over S₀) [GrpObj G₀]
    (b : Sp Qb ⟶ S₀) (g : A₀.left ⟶ G₀.left) (hg : IsGrpPullback A₀ G₀ b g) :
    ∃ (X₀ : Obj F 𝔠 (Sp Qb)) (p' : X.A.left ⟶ X₀.A.left) (g' : X₀.A.left ⟶ G₀.left),
      X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p' ∧ IsGrpPullback X₀.A G₀ b g' ∧ p' ≫ g' = p ≫ g := by
  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  haveI := hA₀.comm
  obtain ⟨rm, hrm⟩ := ActDescent.exists_oAct hp X.rm fun a ↦ by
    obtain ⟨f, -, hf⟩ := GlobalTheory.HomDescentQb.hom_descends A₀ A₀ X.A X.A p p _ _ hA₀ gA₀ hA₀ gA₀ hp hp (X.rm.act a) (X.rm.hom a)
    exact ⟨f, hf⟩
  obtain ⟨D₀, _, Q, D, _, d, m, hD₀, gD₀, q₀, q₀', hd, m₁, m₂, q, q'⟩ := exists_dual_pair HD hA₀ gA₀ hp
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod X.ab X.ab (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
    (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv X.ab X.ab hH aH (X.isLB c) (X.rig₁ c) (X.rig₂ c)
    obtain ⟨x, hx, ex⟩ := exists_hom q q' (X.isLB c) a₁ a₂
    obtain ⟨x₀, hx₀, e₀⟩ := GlobalTheory.HomDescentQb.hom_descends A₀ D₀ X.A D p d _ _ hA₀ gA₀ hD₀ gD₀ hp hd x hx
    obtain ⟨b₁, b₂⟩ := additive_ev q₀.isLB q₀.additive q₀'.additive x₀
    refine ⟨_, pull_isLB q₀.isLB _, b₁, b₂, ?_⟩
    rw [cls_ev q₀.isLB, ex]
    exact pull_evc_eq l₁ l₂ m₁ m₂ q₀.isLB q.isLB e₀.symm
  choose P₀ hP₀ a₁ a₂ eP using hx
  have inj : ∀ {P P' : LB (A₀ ⊗ A₀).left} (hP : P.IsLB) (hP' : P'.IsLB), IsAdditive P → IsAdditive P' →
      CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP') → LBIso P P' := fun hP hP' a a' e ↦
    (cls_eq_iff hP hP').1 (cls_eq_of_pull hp.1 hd l₁ l₂ m₁ m₂ q₀ q hP hP' a a' e)
  have iso : ∀ c, LBIso ((P₀ c).pull l) (X.P c) := fun c ↦
    (cls_eq_iff (pull_isLB (hP₀ c) _) (X.isLB c)).1 (by rw [cls_pull (hP₀ c)]; exact eP c)

  have val : ∀ (c : 𝔠.elt) {Y₀ : Over (Sp Qb)} {Y : Over (Sp ℂ)} (r : Y.left ⟶ Y₀.left) (a₀ t₀ : Y₀ ⟶ A₀)
      (a t : Y ⟶ X.A), a.left ≫ p = r ≫ a₀.left → t.left ≫ p = r ≫ t₀.left →
      CechPic.pull r (evc (hP₀ c) a₀ t₀) = evc (X.isLB c) a t := fun c Y₀ Y r a₀ t₀ a t ha ht ↦ by
    rw [evc, evc, ← eP, ← pull_comp, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₁, lift_left_fst_assoc, ha]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₂, lift_left_snd_assoc, ht]
  refine ⟨{ A := A₀
            ab := hA₀
            dim := gA₀
            rm := rm
            P := P₀
            isLB := hP₀
            rig₁ := fun c ↦ triv_left (hP₀ c) (a₁ c)
            rig₂ := fun c ↦ triv_right (hP₀ c) (a₂ c)
            symm := fun c ↦ ?_
            add := fun c c' ↦ ?_
            smul := fun a c ↦ ?_
            pos := fun c hc ↦ ?_
            ker := fun c T₀ x hx a ha ↦ ?_ }, p, g, ⟨hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩, hg, rfl⟩
  · refine inj (hP₀ c) (pull_isLB (hP₀ c) _) (a₁ c) (a₂ c) ?_
    rw [eP, cls_ev (hP₀ c), val c l _ _ _ _ l₂.symm l₁.symm]
    exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.symm c)
  · have hq := LB.isLB_div (hP₀ (c + c')) (hP₀ c)
    have ev' : ∀ (Y : Over (Sp Qb)) (a t : Y ⟶ A₀), evc hq a t = evc (hP₀ (c + c')) a t - evc (hP₀ c) a t :=
      fun Y a t ↦ by rw [evc, cls_div (hP₀ (c + c')) (hP₀ c), map_sub]; rfl
    refine inj (hP₀ c') hq (a₁ c') ((isAdditive_iff hq).2 fun Y a a' t ↦ ?_) ?_
    · rw [ev', ev', ev', (isAdditive_iff (hP₀ _)).1 (a₁ _), (isAdditive_iff (hP₀ _)).1 (a₁ _)]
      abel
    · rw [cls_div (hP₀ (c + c')) (hP₀ c), map_sub, eP, eP, eP, ← cls_div (X.isLB (c + c')) (X.isLB c)
        (LB.isLB_div (X.isLB (c + c')) (X.isLB c))]
      exact (cls_eq_iff _ _).2 (X.add c c')
  · have hq : (ev (P₀ c) (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a)).IsLB := pull_isLB (hP₀ c) _
    refine inj (hP₀ _) hq (a₁ _) ((isAdditive_iff hq).2 fun Y u u' t ↦ ?_) ?_
    · simp only [evc_ev (hP₀ c), lift_fst, lift_snd_assoc]
      exact (isAdditive_iff (hP₀ c)).1 (a₁ c) _ _ _ _
    · rw [eP, cls_ev (hP₀ c), val c l _ _ (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) l₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hrm, ← Category.assoc, ← Category.assoc, l₂])]
      exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  · refine AmpleDescent.relAmple_of_fieldExtension Qb ℂ _ A₀ X.A p _ _ hA₀ hp (pull_isLB (hP₀ c) _)
      (pull_isLB (X.isLB c) _) ((cls_eq_iff (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (hP₀ c) _) _)).1 ?_)
      (X.pos c hc)
    rw [cls_pull (pull_isLB (hP₀ c) _), cls_ev (hP₀ c), cls_ev (X.isLB c)]
    exact (val c p _ _ _ _ (by simp) (by simp)).symm
  · let T : Over (Sp ℂ) := (Over.pullback (spMap (algebraMap Qb ℂ))).obj T₀
    let r : T.left ⟶ T₀.left := Limits.pullback.fst _ _
    have hr : IsPullback r T.hom T₀.hom (spMap (algebraMap Qb ℂ)) := IsPullback.of_hasPullback _ _
    have w : (r ≫ x.left) ≫ A₀.hom = T.hom ≫ spMap (algebraMap Qb ℂ) := by rw [Category.assoc, Over.w x, hr.w]
    let x' : T ⟶ X.A := liftPt hp T.hom _ w
    have ex : x'.left ≫ p = r ≫ x.left := liftPt_left hp _ _ w
    let u : Over.mk ((X.A ⊗ T).hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk ((snd X.A T).left ≫ r) (by
      change ((snd X.A T).left ≫ r) ≫ T₀.hom = _
      rw [Category.assoc, hr.w, ← Category.assoc, Over.w]
      rfl)
    let s : (X.A ⊗ T).left ⟶ (A₀ ⊗ T₀).left := (lift (pushP hp (s := (X.A ⊗ T).hom) rfl (fst X.A T)) u).left
    have s₁ : s ≫ (fst A₀ T₀).left = (fst X.A T).left ≫ p := lift_left_fst _ _
    have s₂ : s ≫ (snd A₀ T₀).left = (snd X.A T).left ≫ r := lift_left_snd _ _
    have z : evc (X.isLB c) (fst X.A T) (snd X.A T ≫ x') = 0 := by
      rw [← val c s (fst A₀ T₀) (snd A₀ T₀ ≫ x) _ _ s₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, ex, ← Category.assoc, ← Category.assoc, s₂]),
        (triv_ev_iff (hP₀ c) _ _).1 hx, map_zero]
    have k := X.ker c T x' ((triv_ev_iff (X.isLB c) _ _).2 z) a ha
    refine ActDescent.over_hom_ext hr ?_
    rw [Over.comp_left, ← Category.assoc, ← ex, Category.assoc, ← hrm, ← Category.assoc, ← Over.comp_left, k]
    refine (one_left_comp hp (s := T.hom) rfl).trans ?_
    let r' : Over.mk (T.hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk r hr.w
    exact congrArg (fun y ↦ y.left) (MonObj.comp_one (M := A₀) r').symm
  · exact (cls_eq_iff (X.isLB c) (pull_isLB (hP₀ c) _)).1 (by rw [cls_pull (hP₀ c)]; exact (eP c).symm)

end GlobalTheory.CMModel

end ModelOver

namespace GlobalTheory.CMModel

open GlobalTheory.ComplexPoints
open scoped CategoryTheory.Obj

theorem exists_qbModel_of_subring : GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (L : Set E) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (R₀ : Subring ℂ) (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left), IsAbelianScheme G₀ →
      IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ →
    ∃ (XQ : Obj (FR E) 𝔠 (Sp Qb)) (pQ : X.A.left ⟶ XQ.A.left) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct (orderC c) XQ.A),
      X.IsPullBy XQ (spMap (algebraMap Qb ℂ)) pQ ∧ IsGrpPullback XQ.A G₀ (spMap σ) gQ ∧ pQ ≫ gQ = p₀ ∧
      (∀ a : OF E, cmQ.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = XQ.rm.act a) ∧
      ∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
        (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ pQ = pQ ≫ (cmQ.act a).left := by
  intro HD E _ _ _ I _ φ c L 𝔠 X U hα R₀ σ hσ G₀ _ p₀ _ hpb

  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  have hring : R₀.subtype = (algebraMap Qb ℂ).comp σ := RingHom.ext fun x ↦ (hσ x).symm
  have hcomp : spMap R₀.subtype = spMap (algebraMap Qb ℂ) ≫ spMap σ := by
    rw [hring]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let A₀ : Over (Sp Qb) := (Over.pullback (spMap σ)).obj G₀
  letI : GrpObj A₀ := inferInstanceAs (GrpObj ((Over.pullback (spMap σ)).obj G₀))
  have hA₀G : IsGrpPullback A₀ G₀ (spMap σ) (pullback.fst G₀.hom (spMap σ)) := isGrpPullback_pullback G₀ (spMap σ)
  let p : X.A.left ⟶ A₀.left := pullback.lift p₀ (X.A.hom ≫ spMap (algebraMap Qb ℂ)) (by
    rw [Category.assoc, ← hcomp]; exact hpb.1.w)
  have hp₁ : p ≫ pullback.fst G₀.hom (spMap σ) = p₀ := pullback.lift_fst _ _ _
  have hp₂ : p ≫ A₀.hom = X.A.hom ≫ spMap (algebraMap Qb ℂ) := pullback.lift_snd _ _ _
  have hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p :=
    IsGrpPullback.cancel hA₀G (by rw [hp₁, ← hcomp]; exact hpb) hp₂
  obtain ⟨hA₀, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend Qb ℂ (algebraMap Qb ℂ) A₀ X.A p hp X.ab

  obtain ⟨XQ, pQ, gQ, hXQ, hgQ, hpg⟩ := exists_obj_of_isGrpPullback_over HD.1 X U.c U.pos A₀ p hA₀ (hdim _ X.dim) hp
    G₀ (spMap σ) _ hA₀G

  let ρ : orderC c →+* Module.End ℂ (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    (Algebra.lmul ℂ (Fin (Module.finrank ℚ (FR E)) → ℂ)).toRingHom.comp
      ((Pi.ringHom fun j ↦ φ (U.e j)).comp (orderC c).subtype)
  have hρ : ∀ a w, ρ a w = fun j ↦ φ (U.e j) (a : E) * w j := fun a w ↦ rfl
  have hlat : ∀ a, ∀ z ∈ U.u.Λ, ρ a z ∈ U.u.Λ := fun a z hz ↦ by
    obtain ⟨α, hαm, hαe⟩ := hα a
    haveI := hαm
    rw [← U.u.ker] at hz ⊢
    rw [hρ, hαe, hz, MonObj.one_comp]
  obtain ⟨act, hact⟩ := GlobalTheory.TorusAction.exists_oAct_of_map_lattice _ X.A X.ab _ U.u (orderC c) ρ hlat
  haveI := X.ab.smooth
  haveI := X.ab.proper
  haveI : IsReduced X.A.left := isReduced_of_smooth_complex _ X.A.hom X.ab.smooth
  have hext : ∀ f f' : X.A ⟶ X.A, (∀ z, U.u.ex z ≫ f = U.u.ex z ≫ f') → f = f' := fun f f' h ↦
    over_hom_ext_of_complexPoints fun x ↦ by
      obtain ⟨z, rfl⟩ := U.u.ex_onto x
      exact h z
  have huniq : ∀ (a : orderC c) (α : X.A ⟶ X.A),
      (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α = act.act a := fun a α h ↦
    hext _ _ fun z ↦ by rw [← h, ← hact, hρ]

  obtain ⟨cmQ, hcm⟩ := GlobalTheory.ActDescent.exists_oAct hXQ.grp act fun a ↦ by
    haveI := act.hom a
    obtain ⟨β, -, hβ⟩ := GlobalTheory.RealMult.Obj.exists_end_descend_algebraic _ _ XQ X pQ hXQ (act.act a)
    exact ⟨β, hβ⟩
  refine ⟨XQ, pQ, gQ, cmQ, hXQ, hgQ, by rw [hpg, hp₁], fun a ↦ ?_, fun a α _ h ↦ ?_⟩
  · refine GlobalTheory.ActDescent.over_hom_ext hXQ.grp.1 ?_
    rw [← hcm, ← hXQ.act a]
    congr 2
    exact (huniq _ _ (U.act a)).symm
  · rw [huniq a α h]
    exact hcm a

end GlobalTheory.CMModel
