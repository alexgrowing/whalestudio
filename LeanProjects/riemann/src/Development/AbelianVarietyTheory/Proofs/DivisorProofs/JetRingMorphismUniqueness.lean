import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section Gen

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem corrForm_antisymm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x := by
  obtain ⟨n, a, b, hc, hφ⟩ := id H
  let s : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)
  have ms : IsMor κ ((A ⊗ A).hom ≫ t) κ ((A ⊗ A).hom ≫ t) (RingHom.id R) s.left :=
    IsMor.of_over κ (φ := s.left) (by rw [← Category.assoc, Over.w])
  have hz := isChern_pull ms hc
  rw [crystallinePull2_sum_cup s ms] at hz
  simp only [pullOver_pullOver, s, lift_fst, lift_snd] at hz
  have e' : LBIso (P.pull s.left) P :=
    (cls_eq_iff (pull_isLB hP _) hP).1 ((cls_eq_iff hP (pull_isLB hP _)).2 hs).symm
  have hz' := (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ (pull_isLB hP _) hP e' _ hz
  have H' : IsCorrForm κ t A A P (-φ.flip) := by
    refine ⟨n, fun k ↦ -b k, a, (congrArg (IsChern κ ((A ⊗ A).hom ≫ t) P) ?_).mp hz', fun u v ↦ ?_⟩
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Submodule.coe_neg, map_neg, LinearMap.map_neg, LinearMap.neg_apply]
      exact (neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)).symm
    · simp only [LinearMap.neg_apply, LinearMap.flip_apply]
      rw [hφ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_neg, neg_mul, mul_comm]
  have e := congrArg (fun f ↦ f x y) (H.unique C hP H')
  simpa using e

end Gen

section Jet

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

theorem cupSquare_jet (HR : AbelianDeRham) (HD : AbelianDualCrystal) (J : JetRing R I n) {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    CupSquare J.κ (spMap J.π) (A ⊗ A) := by
  obtain ⟨A', _, ψ, hψ⟩ := FlagTan.exists_isGrpPullback A (spMap (algebraMap R J.B))
  have e : (𝟙 (Sp R)) = spMap J.π ≫ spMap (algebraMap R J.B) := by
    rw [← GlobalTheory.Cris.spMap_comp]
    have : J.π.comp (algebraMap R J.B) = RingHom.id R := RingHom.ext fun r ↦ JetRing.π_algebraMap J r
    rw [this, GlobalTheory.Cris.spMap_id]
  have hn := (GlobalTheory.CrysConn.isGrpPullback_refl A).congr e rfl
  let i' : A.left ⟶ A'.left :=
    hψ.1.lift (Over.Hom.left (𝟙 A)) (A.hom ≫ spMap J.π) (hn.1.w.trans (Category.assoc _ _ _).symm)
  have ei : i' ≫ ψ = Over.Hom.left (𝟙 A) := hψ.1.lift_fst _ _ _
  have h' : IsGrpPullback A A' (spMap J.π) i' := hψ.cancel (hn.congr rfl ei.symm) (hψ.1.lift_snd _ _ _)
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA hψ
  have hg' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 hg
  exact AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 J.nil (fun r ↦ ⟨algebraMap R J.B r, JetRing.π_algebraMap J r⟩)
    rfl hA' hg' hA' hg' h' h'

end Jet

section Diag

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem polForm_diag {P : LB (A ⊗ A).left} {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (H : IsCorrForm (dp0 R) (𝟙 _) A A P φ) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A (P.pull (lift (𝟙 A) (𝟙 A)).left) ψ ∧ ∀ x y, ψ x y = φ x y - φ y x := by
  obtain ⟨ψ', hψ', eψ'⟩ := H.isPolForm
  obtain ⟨ψ, hψ, eψ⟩ := hψ'.pull (homMor (dp0 R) (𝟙 _) (lift (𝟙 A) (𝟙 A)))
  refine ⟨ψ, hψ, fun x y ↦ ?_⟩
  rw [eψ (push (dp0 R) (𝟙 _) (lift (𝟙 A) (𝟙 A)) x) x (push (dp0 R) (𝟙 _) (lift (𝟙 A) (𝟙 A)) y) y
    (fun _ ↦ rfl) (fun _ ↦ rfl), RingHom.id_apply, eψ', push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_id]
  rfl

end Diag

section Props

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  {I : Type} [Fintype I]

theorem form_props (HR : AbelianDeRham) (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A)) (hN : admitted X N)
    (c : 𝔠.elt) :
    ∃ φ₀ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ₀ ∧
      (∀ x ∈ Fil X.A, ∀ y ∈ Fil X.A, φ₀ x y = 0) ∧ (∀ i x y, φ₀ (N i x) y + φ₀ x (N i y) = 0) ∧
      ∀ i j x y, φ₀ (N i x) (N j y) = 0 := by
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C (X.isLB c) (X.rig₁ c) (X.rig₂ c)
  have anti := corrForm_antisymm C (X.isLB c) (X.symm c) hφ₀
  obtain ⟨ψ, hψ, eψ⟩ := polForm_diag hφ₀
  have two : ∀ x y, ψ x y = 2 * φ₀ x y := fun x y ↦ by rw [eψ, anti y x]; ring
  have canc : ∀ r : R, 2 * r = 0 → r = 0 := fun r h ↦ (mul_eq_zero.1 h).resolve_left two_ne_zero
  obtain ⟨s1, s2⟩ := hN.2.2 c ψ hψ
  have iso := (HR.2.2.2.2 R X.A _ X.ab X.dim (X.diag c) (pull_isLB (X.isLB c) _) ψ hψ).1
  refine ⟨φ₀, hφ₀, fun x hx y hy ↦ canc _ (by rw [← two]; exact iso x hx y hy), fun i x y ↦ canc _ ?_,
    fun i j x y ↦ canc _ ?_⟩
  · rw [mul_add, ← two, ← two]; exact s1 i x y
  · rw [← two]; exact s2 i j x y

end Props

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem ext_of_isBC {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ} (hm : m.IsBC) {d₁ d₂ : Crys κ' t' A'}
    (h : ∀ c, d₁ (m.pull c) = d₂ (m.pull c)) : d₁ = d₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

end BC

theorem jetFil_isotropic : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (c : 𝔠.elt) (φ : Crys J.κ (spMap J.π) X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A →ₗ[J.B] J.B),
        GlobalTheory.AbDual.IsCorrForm J.κ (spMap J.π) X.A X.A (X.P c) φ → ∀ a ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, ∀ b ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, φ a b = 0 := by
  intro HG HR HD F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m c φ hφ
  have hm := isBC_jetRing HG HR HD F 𝔠 R I n J X m
  obtain ⟨φ₀, hφ₀, z0, z1, z2⟩ := form_props HR X N hN c
  have iso : LBIso ((X.P c).pull (Over.Hom.left (𝟙 (X.A ⊗ X.A)))) (X.P c) :=
    (cls_eq_iff (pull_isLB (X.isLB c) _) (X.isLB c)).1 (by rw [cls_pull (X.isLB c), Over.id_left, CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ₀.pull (X.isLB c) m m (h := Over.Hom.left (𝟙 (X.A ⊗ X.A))) (by simp) (by simp)
    (X.isLB c) iso
  have eφ := hφ.unique (cupSquare_jet HR HD J X.ab X.dim) (X.isLB c) hφ'
  have hv : ∀ u c, hm.bcMap u (m.pull c) = algebraMap R J.B (u c) := fun u ↦ hm.corr_iff.2 rfl
  have hb : ∀ u v, φ (hm.bcMap u) (hm.bcMap v) = algebraMap R J.B (φ₀ u v) := fun u v ↦ by
    rw [eφ]; exact e' _ _ _ _ (hm.corr_iff.2 rfl) (hm.corr_iff.2 rfl)
  have hd : ∀ x d, IsJetElt J X N m x d → d = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := fun x d hx ↦
    ext_of_isBC hm fun c ↦ by
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hv]
      exact hx c
  have key : ∀ x ∈ Fil X.A, ∀ y ∈ Fil X.A, ∀ d d', IsJetElt J X N m x d → IsJetElt J X N m y d' → φ d d' = 0 := by
    intro x hx y hy d d' hdx hdy
    rw [hd x d hdx, hd y d' hdy]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hb, z0 x hx y hy, z2, map_zero, mul_zero, Finset.sum_const_zero, add_zero,
      zero_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [← mul_add, ← map_add, z1, map_zero, mul_zero]
  intro a ha b hb
  induction ha using Submodule.span_induction generalizing b with
  | mem a ha' =>
    obtain ⟨x, hx, hxa⟩ := ha'
    induction hb using Submodule.span_induction with
    | mem b hb' =>
      obtain ⟨y, hy, hyb⟩ := hb'
      exact key x hx y hy a b hxa hyb
    | zero => exact map_zero _
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | smul r u _ hu => rw [map_smul, hu, smul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add u v _ _ hu hv => rw [map_add, LinearMap.add_apply, hu b hb, hv b hb, add_zero]
  | smul r u _ hu => rw [map_smul, LinearMap.smul_apply, hu b hb, smul_zero]

end GlobalTheory.JetIsotropic
