import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

open GlobalTheory.AbLaw GlobalTheory.GrpTangent TensorProduct
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R]

def ResSurj.{u} : Prop :=
  ∀ (R : Type) [CommRing R] (H : Type 1) [AddCommGroup H] [Module R H] (M : Type u) [AddCommGroup M] [Module R M]
    (g : ℕ) (F N : Submodule R H), IsCompl F N → Module.Finite R H → Module.Projective R H →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk H p = 2 * g) → Module.Finite R F → Module.Projective R F →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk F p = g) → Module.Finite R M → Module.Projective R M →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) → ∀ gam : H →ₗ[R] M,
    (∀ m : Ideal R, m.IsMaximal → ∀ q : H, gam q ∈ m • (⊤ : Submodule R M) → q ∈ F ⊔ m • (⊤ : Submodule R H)) →
    Function.Surjective gam

theorem cst_top {Y : Scheme.{0}} (f : Y ⟶ Sp R) (r : R) :
    cst f ⊤ r = f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rs_self _ _

theorem cst_comp {Y Y' : Scheme.{0}} (ψ : Y' ⟶ Y) (f : Y ⟶ Sp R) (r : R) :
    cst (ψ ≫ f) ⊤ r = ψ.appTop.hom (cst f ⊤ r) := by
  rw [cst_top, cst_top, Scheme.Hom.comp_appTop]; rfl

theorem cst_spMap {R' : Type} [CommRing R'] {Y : Scheme.{0}} (t : Y ⟶ Sp R') (ρ : R →+* R') (r : R) :
    cst (t ≫ spMap ρ) ⊤ r = cst t ⊤ (ρ r) := by
  rw [cst_top, cst_top, Scheme.Hom.comp_appTop]
  have e := congrArg (fun q ↦ q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  exact congrArg t.appTop.hom e.symm

section Mod

variable {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem pull_w {R' : Type} [CommRing R'] {σ : R →+* R'} {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap σ) φ) : φ ≫ A.hom ≫ 𝟙 _ = (A'.hom ≫ 𝟙 _) ≫ spMap σ := by
  rw [Category.comp_id, Category.comp_id]; exact h.1.w

theorem mem_sup_of_pullP (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (m : Ideal R) {A' : Over (Sp (R ⧸ m))} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap R (R ⧸ m))) φ) (q : primDR A)
    (hq : pullP (pull_w h) (toP _ q.1) = 0) : q ∈ PrimitiveSubmodule A ⊔ m • (⊤ : Submodule R (primDR A)) := by
  obtain ⟨hbc, hF⟩ := hB R A g hA hg (R ⧸ m) A' φ h
  have h1 : (AbelianDeRham.bcMor h).pull q ∈ PrimitiveSubmodule A' :=
    (toP_eq_zero_iff _).1 ((pullP_toP (AbelianDeRham.bcMor h).isMor q.1).symm.trans hq)
  rw [hF] at h1
  have h2 : ∀ z ∈ Submodule.span (R ⧸ m) ((AbelianDeRham.bcMor h).pull '' (PrimitiveSubmodule A)),
      ∃ f ∈ PrimitiveSubmodule A, (AbelianDeRham.bcMor h).pull f = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨r • a, Submodule.smul_mem _ _ ha, LinearMap.map_smulₛₗ _ _ _⟩
  obtain ⟨f, hf, e⟩ := h2 _ h1
  have h3 : (1 : R ⧸ m) ⊗ₜ[R] (q - f) = 0 := hbc.1 (by
    rw [liftSemi_tmul, one_smul, map_sub, e, sub_self, map_zero])
  have h4 := congrArg (TensorProduct.quotTensorEquivQuotSMul (primDR A) m) h3
  rw [map_zero, ← map_one (Ideal.Quotient.mk m), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul,
    Submodule.Quotient.mk_eq_zero] at h4
  rw [← add_sub_cancel f q]
  exact Submodule.add_mem_sup hf h4

theorem surj_of_gamma (hR : ResSurj.{0}) (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge)
    (hB : AbelianDeRham.BaseChange) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {M : Type} [AddCommGroup M] [Module R M] (h₁ : Module.Finite R M) (h₂ : Module.Projective R M)
    (h₃ : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) (gam : H1OnPoints (A.hom ≫ 𝟙 _) →ₗ[R] M)
    (hgam : Function.Injective gam)
    (hm : ∀ (m : Ideal R) (A' : Over (Sp (R ⧸ m))) [GrpObj A'] (φ : A'.left ⟶ A.left)
      (h : IsGrpPullback A' A (spMap (algebraMap R (R ⧸ m))) φ) (c : H1OnPoints (A.hom ≫ 𝟙 _)),
      gam c ∈ m • (⊤ : Submodule R M) → pullP (pull_w h) c = 0) :
    Function.Surjective (toP (A.hom ≫ 𝟙 _)) := by
  obtain ⟨a₁, a₂, a₃⟩ := hF.prim hA hg
  obtain ⟨-, ⟨N, hN⟩, b₁, b₂, b₃⟩ := hH R A g hA hg
  have hs := hR R (primDR A) M g (PrimitiveSubmodule A) N hN a₁ a₂ a₃ b₁ b₂ b₃ h₁ h₂ h₃
    (gam ∘ₗ toP _ ∘ₗ (primDR A).subtype) fun m _ q hq ↦
      mem_sup_of_pullP hB hA hg m (isGrpPullback_pullback A _) q (hm m _ _ (isGrpPullback_pullback A _) _ hq)
  intro c
  obtain ⟨q, hq⟩ := hs (gam c)
  exact ⟨q.1, hgam hq⟩

end Mod

section Gamma

variable {E : ETy} (hE : IsE @E) {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem E_congr {X Y : Scheme.{0}} (s : X ⟶ Sp R) (c : H1OnPoints s) {π π' : Y ⟶ X} {ν ν' : Γ(Y, ⊤)} (h : ν * ν = 0)
    (h' : ν' * ν' = 0) (e : π = π') (e' : ν = ν') : E s c π ν h = E s c π' ν' h' := by
  subst e e'; rfl

include hE in
theorem E_zero {X Y : Scheme.{0}} (s : X ⟶ Sp R) (π : Y ⟶ X) (ν : Γ(Y, ⊤)) (h : ν * ν = 0) : E s 0 π ν h = 0 := by
  have e := hE.add s 0 0 π ν h
  rw [add_zero] at e
  exact left_eq_add.1 e

variable (E) in

def Ec (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ epsR R) : Pic Y.left :=
  E (A.hom ≫ 𝟙 _) c a.left (epsFn (R := R) t.left) (epsFn_sq _)

omit [GrpObj A] in
include hE in
theorem pull_Ec (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y Z : Over (Sp R)} (u : Z ⟶ Y) (a : Y ⟶ A) (t : Y ⟶ epsR R) :
    GlobalTheory.CechPic.pull u.left (Ec E c a t) = Ec E c (u ≫ a) (u ≫ t) :=
  hE.nat _ c a.left _ _ u.left _ _ (cst_comp u.left t.left _)

include hE in
theorem Ec_one (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y : Over (Sp R)} (t : Y ⟶ epsR R) : Ec E c (1 : Y ⟶ A) t = 0 := by
  have h : (η[A].left : Sp R ⟶ A.left) ≫ A.hom ≫ 𝟙 _ = 𝟙 (Sp R) ≫ spMap (RingHom.id R) := by
    rw [Category.comp_id, GlobalTheory.Cris.spMap_id, Category.comp_id]; exact Over.w η[A]
  have e := hE.chg h c Y.hom (epsFn (R := R) t.left) (epsFn_sq _)
  haveI : IsIso (𝟙 (Sp R)) := IsIso.id _
  rw [H1OnPoints_eq_zero_of_isIso _ (pullP h c), E_zero hE] at e
  exact e.symm

omit [GrpObj A] in
include hE in
theorem Ec_red (c : H1OnPoints (A.hom ≫ 𝟙 _)) {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ epsR R)
    (ht : t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R) : Ec E c a t = 0 := by
  refine hE.zero _ c _ _ _ ?_
  rw [epsFn, ht]
  exact (cst_spMap Y.hom _ _).trans (map_zero _)

omit [GrpObj A] in
include hE in
theorem Ec_smul (c : H1OnPoints (A.hom ≫ 𝟙 _)) (r : R) {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ epsR R) :
    Ec E (r • c) a t = Ec E c a (t ≫ GlobalTheory.GrpTangent.epsScale r) := by
  refine hE.smul _ c r _ _ _ _ _ ?_
  have e : a.left ≫ A.hom ≫ 𝟙 _ = t.left ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [Category.comp_id, Over.w a]; exact (Over.w t).symm
  rw [e]
  refine (cst_spMap (R := DualNumber R) t.left (epsScaleR r) _).trans ?_
  rw [cst_spMap, epsFn, ← map_mul]
  congr 1
  ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

variable {P : LB (A ⊗ B).left} (hP : IsDual A B P)
  (hadd : ∀ {M : LB (A ⊗ epsR R).left} (hM : M.IsLB),
    (∀ (Y : Over (Sp R)) (t : Y ⟶ epsR R), evc hM (1 : Y ⟶ A) t = 0) →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R → evc hM a t = 0) →
    IsAdditive M)

include hE hP hadd in
theorem exists_pt (c : H1OnPoints (A.hom ≫ 𝟙 _)) : ∃ x : epsR R ⟶ B, IsTangent x ∧
    ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), evc hP.isLB a (t ≫ x) = Ec E c a t := by
  obtain ⟨M, hM, eM⟩ := cls_surj (Ec E c (fst A (epsR R)) (snd A (epsR R)))
  have k : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), evc hM a t = Ec E c a t := fun Y a t ↦ by
    rw [evc, eM, pull_Ec hE, lift_fst, lift_snd]
  obtain ⟨x, hx, -⟩ := hP.univ _ M hM (hadd hM (fun Y t ↦ (k Y _ t).trans (Ec_one hE c t))
    fun Y a t ht ↦ (k Y a t).trans (Ec_red hE c a t ht))
  have e : cls M hM = evc hP.isLB (fst A _) (snd A _ ≫ x) := (cls_eq_iff hM (pull_isLB hP.isLB _)).2 hx
  have k' : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), evc hP.isLB a (t ≫ x) = Ec E c a t := fun Y a t ↦ by
    rw [← k, evc, evc, e, pull_evc, lift_fst, lift_snd_assoc, evc]
  refine ⟨x, (isTangent_iff x).2 (hP.eq_one _ ((triv_ev_iff hP.isLB _ _).2 ?_)), k'⟩
  rw [← Category.assoc, k']
  refine Ec_red hE c _ _ ?_
  rw [Over.comp_left, ← Over.w (snd A (𝟙_ (Over (Sp R))))]
  exact congrArg (· ≫ GlobalTheory.DeRham.epsRed R) (Category.comp_id _).symm

include hE hP hadd in
theorem surj_of_isDual' (hR : ResSurj.{0}) (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge)
    (hB : AbelianDeRham.BaseChange) {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hA' : IsAbelianScheme B) (hg' : SmoothOfRelativeDimension g B.hom) (hsw : IsAdditive (swap P)) :
    Function.Surjective (toP (A.hom ≫ 𝟙 _)) := by
  haveI := hA'.comm
  choose x hx k using exists_pt hE hP hadd
  let gam : H1OnPoints (A.hom ≫ 𝟙 _) →ₗ[R] GlobalTheory.Serre.Lie (GlobalTheory.Serre.intAct B) :=
    { toFun := fun c ↦ GlobalTheory.Serre.Lie.mk _ (x c) (hx c)
      map_add' := fun c c' ↦ GlobalTheory.Serre.Lie.ext (GlobalTheory.BirigidLift.dual_ext hP (by
        change evc _ _ (_ ≫ x (c + c')) = evc _ _ (_ ≫ (x c * x c'))
        rw [MonObj.comp_mul, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP.isLB).1 hsw, k, k, k]
        exact hE.add _ _ _ _ _ _))
      map_smul' := fun r c ↦ GlobalTheory.Serre.Lie.ext (GlobalTheory.BirigidLift.dual_ext hP (by
        change evc _ _ (_ ≫ x (r • c)) = evc _ _ (_ ≫ GlobalTheory.GrpTangent.epsScale r ≫ x c)
        rw [← Category.assoc, k, k, Ec_smul hE])) }
  obtain ⟨l₁, l₂, l₃⟩ := GlobalTheory.LieInj.lie_finite_projective B g hg' (GlobalTheory.Serre.intAct B)
  have pb : ∀ {C : Type} [CommRing C] (G : Over (Sp C)), IsPullback (fst G (epsR C)).left (snd G (epsR C)).left
      (G.hom ≫ 𝟙 _) (spMap (algebraMap C (DualNumber C))) := fun G ↦ by
    rw [Category.comp_id]; exact IsPullback.of_hasPullback _ _
  refine surj_of_gamma hR hF hH hB hA hg l₁ l₂ l₃ gam ((injective_iff_map_eq_zero _).2 fun c hc ↦ ?_)
    fun m A' _ φ h c hc ↦ ?_
  · have e : x c = 1 := congrArg GlobalTheory.Serre.Lie.hom hc
    refine hE.inj _ c _ _ (pb A) ((k _ _ _ _).symm.trans ?_)
    rw [e, MonObj.comp_one, evc_one_right hP.isLB hP.zero]
  · let σ := algebraMap R (R ⧸ m)
    let Y : Over (Sp R) := Over.mk ((A' ⊗ epsR (R ⧸ m)).hom ≫ spMap σ)
    let a : Y ⟶ A := Over.homMk ((fst A' (epsR (R ⧸ m))).left ≫ φ) (by
      change (_ ≫ φ) ≫ A.hom = _ ≫ spMap σ
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hc' : (Chart.dualMapR σ).comp (algebraMap R (DualNumber R)) =
        (algebraMap (R ⧸ m) (DualNumber (R ⧸ m))).comp σ := RingHom.ext fun r ↦ by
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    let t : Y ⟶ epsR R := Over.homMk ((snd A' (epsR (R ⧸ m))).left ≫ spMap (Chart.dualMapR σ)) (by
      change (_ ≫ _) ≫ spMap _ = _ ≫ spMap σ
      rw [Category.assoc, ← GlobalTheory.Cris.spMap_comp, hc', GlobalTheory.Cris.spMap_comp, ← Category.assoc]
      exact congrArg (· ≫ spMap σ) (Over.w (snd A' (epsR (R ⧸ m)))))
    have ht : t ≫ (gam c).hom = 1 := by
      refine Submodule.smul_induction_on (p := fun v ↦ t ≫ GlobalTheory.Serre.Lie.hom v = 1) hc (fun r hr v _ ↦ ?_)
        fun v w hv hw ↦ by rw [GlobalTheory.Serre.Lie.hom_add, MonObj.comp_mul, hv, hw, _root_.mul_one]
      have e : t ≫ GlobalTheory.GrpTangent.epsScale r = t ≫ GlobalTheory.GrpTangent.epsScale 0 := by
        refine Over.OverMorphism.ext ?_
        change (_ ≫ spMap _) ≫ spMap (epsScaleR r) = (_ ≫ spMap _) ≫ spMap (epsScaleR 0)
        rw [Category.assoc, Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
        congr 2
        have hr' : σ r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hr
        refine RingHom.ext fun z ↦ ?_
        ext <;> simp [Chart.dualMapR, epsScaleR, hr']
      rw [GlobalTheory.Serre.Lie.hom_smul, ← Category.assoc, e, Category.assoc, epsScale_zero_comp v.isTangent,
        MonObj.comp_one]
    have e0 : Ec E c a t = 0 := by
      rw [← k]
      exact (congrArg (evc hP.isLB a) ht).trans (evc_one_right hP.isLB hP.zero a)
    refine hE.inj _ _ _ _ (pb A') ((hE.chg (pull_w h) c _ _ _).trans (Eq.trans (E_congr _ c _ _ rfl ?_) e0))
    refine Eq.trans ?_ (cst_spMap (R := DualNumber R) _ (Chart.dualMapR σ) _).symm
    rw [epsFn]
    congr 1
    ext <;> simp [Chart.dualMapR]

end Gamma

end CrystallinePoints.Pd
