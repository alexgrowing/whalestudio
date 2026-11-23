import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveLatticePeriodFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentWithUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodMatrixExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientAbelianSchemeDescendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraicStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMModel

theorem cls_eq_of_pull {S S' : Scheme.{0}} {b : S' ⟶ S} [Flat b] [Surjective b] {A B D : Over S} [GrpObj A] [GrpObj D]
    {A' B' D' : Over S'} [GrpObj A'] [GrpObj D'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {d : D'.left ⟶ D.left}
    {l : (A' ⊗ B').left ⟶ (A ⊗ B).left} {m : (A' ⊗ D').left ⟶ (A ⊗ D).left}
    (hg : IsPullback g B'.hom B.hom b) (hd : IsGrpPullback D' D b d)
    (l₁ : l ≫ (fst A B).left = (fst A' B').left ≫ f) (l₂ : l ≫ (snd A B).left = (snd A' B').left ≫ g)
    (m₁ : m ≫ (fst A D).left = (fst A' D').left ≫ f) (m₂ : m ≫ (snd A D).left = (snd A' D').left ≫ d)
    {Q : LB (A ⊗ D).left} (q : IsDual A D Q) (q' : IsDual A' D' (Q.pull m))
    {P P' : LB (A ⊗ B).left} (hP : P.IsLB) (hP' : P'.IsLB) (a : IsAdditive P) (a' : IsAdditive P')
    (e : CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP')) : cls P hP = cls P' hP' := by
  obtain ⟨x, hx, -⟩ := q.univ B P hP a
  obtain ⟨x', hx', -⟩ := q.univ B P' hP' a'
  have ex : cls P hP = evc q.isLB (fst A B) (snd A B ≫ x) := (cls_eq_iff hP (pull_isLB q.isLB _)).2 hx
  have ex' : cls P' hP' = evc q.isLB (fst A B) (snd A B ≫ x') := (cls_eq_iff hP' (pull_isLB q.isLB _)).2 hx'
  have ly : ∀ y : B ⟶ D, ∃ y' : B' ⟶ D', g ≫ y.left = y'.left ≫ d := fun y ↦
    ⟨_, (liftPt_left hd B'.hom (g ≫ y.left) (by rw [Category.assoc, Over.w y, hg.w])).symm⟩
  obtain ⟨y, ey⟩ := ly x
  obtain ⟨y', ey'⟩ := ly x'
  obtain rfl : y = y' := dual_ext q' <| by
    rw [← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey, ← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey', ← ex, ← ex', e]
  obtain rfl : x = x' := ActDescent.over_hom_ext hg (ey.trans ey'.symm)
  exact ex.trans ex'.symm

theorem exists_obj_of_isGrpPullback (HD : GlobalTheory.Published.DualAbelianScheme) {F : Type} [Field F] [NumberField F]
    {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (c₀ : 𝔠.elt) (hc₀ : IsTotPos (c₀ : F)) (A₀ : Over (Sp Qb)) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p) :
    ∃ (X₀ : Obj F 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  haveI := hA₀.comm
  obtain ⟨rm, hrm⟩ := ActDescent.exists_oAct hp X.rm fun a ↦ by
    obtain ⟨f, -, hf⟩ := GlobalTheory.T.homomorphism_descends_to_algebraic A₀ A₀ X.A X.A p p _ _ hA₀ gA₀ hA₀ gA₀ hp hp (X.rm.act a) (X.rm.hom a)
    exact ⟨f, hf⟩
  obtain ⟨D₀, _, Q, D, _, d, m, hD₀, gD₀, q₀, q₀', hd, m₁, m₂, q, q'⟩ := exists_dual_pair HD hA₀ gA₀ hp
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod X.ab X.ab (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
    (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv X.ab X.ab hH aH (X.isLB c) (X.rig₁ c) (X.rig₂ c)
    obtain ⟨x, hx, ex⟩ := exists_hom q q' (X.isLB c) a₁ a₂
    obtain ⟨x₀, hx₀, e₀⟩ := GlobalTheory.T.homomorphism_descends_to_algebraic A₀ D₀ X.A D p d _ _ hA₀ gA₀ hD₀ gD₀ hp hd x hx
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
            ker := fun c T₀ x hx a ha ↦ ?_ }, p, hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩
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

theorem exists_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∃ (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  intro _ _ HD K _ _ d δ io h2 hd hδ E _ _ _ _ I _ φ hφ hio c y hc 𝔠 X U
  obtain ⟨C₀, _, C, _, p, L, u, s, hC₀, gC₀, hp, hL, hs, hu⟩ := GlobalTheory.T.elliptic_curve_lattice_period_form d (io δ) hd (by
    rw [← map_pow, hδ, map_neg, map_natCast])
  obtain ⟨B₀, _, B, _, q, M, v, hB₀, gB₀, hB, gB, hq, hv⟩ :=
    GlobalTheory.T.abelian_scheme_descent_with_uniformization Qb _ C₀ C p L u hC₀ gC₀ hp hL (Module.finrank ℚ (FR E))
  obtain ⟨T, hT, hTΛ⟩ := GlobalTheory.T.cm_period_matrix_exists K d δ io h2 hd hδ E I φ hφ hio c y hc U.e
  obtain ⟨ψ, hψ, eψ⟩ := GlobalTheory.T.lattice_map_gives_homomorphism B X.A _ hB X.ab gB X.dim M _ v U.u (s⁻¹ • T) fun z hz ↦ by
    obtain ⟨x, hx, ex⟩ := hTΛ (s⁻¹ • z) fun j ↦ by
      obtain ⟨a, b, e⟩ := hu _ (hv z hz j)
      exact ⟨a, b, by rw [Pi.smul_apply, e, smul_eq_mul, inv_mul_cancel_left₀ hs]⟩
    refine (U.lat _).2 ⟨x, hx, ?_⟩
    rw [LinearMap.smul_apply, ← map_smul, ex]
    funext j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  obtain ⟨A₀, _, r, hA₀, gA₀, hr⟩ := GlobalTheory.T.quotient_abelian_scheme_descends B₀ B X.A q _ hB₀ gB₀ hq X.ab X.dim ψ hψ fun w ↦ by
    obtain ⟨z, rfl⟩ := U.u.ex_onto w
    obtain ⟨z', rfl⟩ := hT z
    refine ⟨v.ex (s • z'), ?_⟩
    rw [← eψ, LinearMap.smul_apply, map_smul, inv_smul_smul₀ hs]
  exact exists_obj_of_isGrpPullback HD.1 X U.c U.pos A₀ r hA₀ gA₀ hr

end GlobalTheory.CMModel
