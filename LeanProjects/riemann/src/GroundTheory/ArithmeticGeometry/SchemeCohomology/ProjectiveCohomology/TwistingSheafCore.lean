import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory MvPolynomial

universe u

noncomputable section

namespace ProjTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

def upow {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) :
    ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 k)).obj (op (Proj.basicOpen 𝒜 u)) :=
  twistMap hu k (W := Proj.basicOpen 𝒜 u) (fun x => x.2) 1

lemma val_upow {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) (x : Proj.basicOpen 𝒜 u) :
    val (k := k) (U := Proj.basicOpen 𝒜 u) (upow 𝒜 hu k) x = twistFrac u k x.1 x.2 := by
  change twistFrac u k x.1 x.2 * ((1 : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj
    (op (Proj.basicOpen 𝒜 u))).1 x).val = _
  erw [Proj.one_apply, HomogeneousLocalization.val_one, mul_one]

theorem isBasisOn_upow {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) :
    IsBasisOn ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 k)) (Proj.basicOpen 𝒜 u) (upow 𝒜 hu k) := by
  intro V h
  have hW : ∀ x : V, u ∉ x.1.asHomogeneousIdeal := fun x => h x.2
  have e : ∀ r : ringOn (Proj 𝒜) V,
      r • resM ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 k)) h (upow 𝒜 hu k) =
        twistMap hu k (W := V) hW r := by
    intro r
    apply ProjTwist.ext (k := k) (U := V)
    funext x
    change (r.1 x).val * val (k := k) (U := Proj.basicOpen 𝒜 u) (upow 𝒜 hu k) ⟨x.1, h x.2⟩ =
      twistFrac u k x.1 (hW x) * (r.1 x).val
    rw [val_upow, mul_comm]
  have hb := twistMap_bijective hu k (W := V) hW
  refine ⟨fun a b hab => hb.1 ?_, fun s => ?_⟩
  · rw [← e, ← e]
    exact hab
  · obtain ⟨r, hr⟩ := hb.2 s
    exact ⟨r, (e r).trans hr⟩

def ratio {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) : Γ(Proj 𝒜, Proj.basicOpen 𝒜 u) :=
  (Proj.awayToSection 𝒜 u).hom (HomogeneousLocalization.mk ⟨1, ⟨v, hv⟩, ⟨u, hu⟩, ⟨1, pow_one u⟩⟩)

lemma ratio_apply {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (x : Proj.basicOpen 𝒜 u) :
    (ratio 𝒜 hu hv).1 x = HomogeneousLocalization.mk ⟨1, ⟨v, hv⟩, ⟨u, hu⟩, x.2⟩ :=
  rfl

lemma ratio_apply_val {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (x : Proj.basicOpen 𝒜 u) :
    ((ratio 𝒜 hu hv).1 x).val = Localization.mk v ⟨u, x.2⟩ := by
  rw [ratio_apply, HomogeneousLocalization.val_mk]

variable {𝒜}

theorem basicOpen_ratio {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) :
    (Proj 𝒜).basicOpen (ratio 𝒜 hu hv) = Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v := by
  ext x
  change x ∈ (Proj 𝒜).basicOpen (ratio 𝒜 hu hv) ↔ x ∈ Proj.basicOpen 𝒜 u ∧ x ∈ Proj.basicOpen 𝒜 v
  rw [Scheme.mem_basicOpen'']
  constructor
  · rintro ⟨hx, hunit⟩
    refine ⟨hx, ?_⟩
    have h1 := hunit.map (Proj.stalkIso' 𝒜 x)
    change IsUnit (Proj.stalkIso' 𝒜 x ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ _ x hx
      (ratio 𝒜 hu hv))) at h1
    erw [Proj.stalkIso'_germ] at h1
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at h1
    erw [ratio_apply_val] at h1
    rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at h1
    exact h1
  · rintro ⟨hx, hv'⟩
    refine ⟨hx, ?_⟩
    have h1 : IsUnit (Proj.stalkIso' 𝒜 x ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ _ x hx
        (ratio 𝒜 hu hv))) := by
      erw [Proj.stalkIso'_germ]
      rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
      erw [ratio_apply_val]
      rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
      exact hv'
    have h2 := h1.map (Proj.stalkIso' 𝒜 x).symm
    rw [RingEquiv.symm_apply_apply] at h2
    exact h2

theorem ratio_self {u : A} (hu : u ∈ 𝒜 1) : ratio 𝒜 hu hu = 1 := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  erw [ratio_apply_val, Proj.one_apply, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem ratio_mul_ratio' {u v w : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (hw : w ∈ 𝒜 1) :
    resR (inf_le_right : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 v)
        (ratio 𝒜 hv hw) *
      resR (inf_le_left : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 u)
        (ratio 𝒜 hu hv) =
    resR (inf_le_left : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 u)
        (ratio 𝒜 hu hw) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((ratio 𝒜 hv hw).1 ⟨x.1, x.2.2⟩ * (ratio 𝒜 hu hv).1 ⟨x.1, x.2.1⟩).val =
    ((ratio 𝒜 hu hw).1 ⟨x.1, x.2.1⟩).val
  rw [HomogeneousLocalization.val_mul]
  erw [ratio_apply_val, ratio_apply_val, ratio_apply_val]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

theorem upow_res {u v : A} (hu : u ∈ 𝒜 1) (hv : v ∈ 𝒜 1) (m : ℕ) :
    resM ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 m))
        (inf_le_right : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 v)
        (upow 𝒜 hv m) =
      resR (inf_le_left : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 u)
          (ratio 𝒜 hu hv) ^ m •
        resM ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 m))
          (inf_le_left : Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v ≤ Proj.basicOpen 𝒜 u)
          (upow 𝒜 hu m) := by
  apply ProjTwist.ext (k := m) (U := Proj.basicOpen 𝒜 u ⊓ Proj.basicOpen 𝒜 v)
  funext x
  change val (k := m) (U := Proj.basicOpen 𝒜 v) (upow 𝒜 hv m) ⟨x.1, x.2.2⟩ =
    (((ratio 𝒜 hu hv).1 ⟨x.1, x.2.1⟩) ^ m).val *
      val (k := m) (U := Proj.basicOpen 𝒜 u) (upow 𝒜 hu m) ⟨x.1, x.2.1⟩
  rw [val_upow, val_upow, HomogeneousLocalization.val_pow]
  erw [ratio_apply_val]
  simp only [twistFrac, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, Localization.mk_pow,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one,
    one_mul, mul_one]; ring⟩

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

lemma twistFrac_mul (u : A) (a b : ℤ) (x : ProjectiveSpectrum 𝒜)
    (hx : u ∉ x.asHomogeneousIdeal) :
    twistFrac u a x hx * twistFrac u b x hx = twistFrac u (a + b) x hx := by
  rw [twistFrac, twistFrac, twistFrac, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, ← pow_add]
  congr 1
  omega

def mulSec {a b : ℤ} {U : (Proj 𝒜).Opens} (s : Γ(twistingSheaf 𝒜 a, U))
    (t : Γ(twistingSheaf 𝒜 b, U)) : Γ(twistingSheaf 𝒜 (a + b), U) :=
  mkSection (val s * val t) (isLocallyFraction_mul rfl (isLocallyFraction_val s)
    (isLocallyFraction_val t))

@[simp] lemma val_mulSec {a b : ℤ} {U : (Proj 𝒜).Opens} (s : Γ(twistingSheaf 𝒜 a, U))
    (t : Γ(twistingSheaf 𝒜 b, U)) (x : U) : val (mulSec s t) x = val s x * val t x := rfl

def mulLin (a b : ℤ) (U : (Proj 𝒜).Opens) :
    ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 a)).obj (op U) →ₗ[ringOn (Proj 𝒜) U]
      ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 b)).obj (op U) →ₗ[ringOn (Proj 𝒜) U]
        ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 (a + b))).obj (op U) :=
  LinearMap.mk₂ _ (fun s t => mulSec s t)
    (fun s s' t => ProjTwist.ext (funext fun x => by
      change (val s x + val s' x) * val t x = val s x * val t x + val s' x * val t x
      ring))
    (fun r s t => ProjTwist.ext (funext fun x => by
      change ((r.1 x).val * val s x) * val t x = (r.1 x).val * (val s x * val t x)
      ring))
    (fun s t t' => ProjTwist.ext (funext fun x => by
      change val s x * (val t x + val t' x) = val s x * val t x + val s x * val t' x
      ring))
    (fun r s t => ProjTwist.ext (funext fun x => by
      change val s x * ((r.1 x).val * val t x) = (r.1 x).val * (val s x * val t x)
      ring))

variable (𝒜) in

def mulPre (a b : ℤ) :
    (preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 a) ⊗ (preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 b) ⟶
      (preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 (a + b)) where
  app U := ModuleCat.ofHom
    (X := ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 a) ⊗
      (preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 b)).obj U)
    (Y := ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 (a + b))).obj U)
    (by exact TensorProduct.lift (mulLin a b U.unop))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    exact ProjTwist.ext (funext fun x => rfl)

variable (𝒜) in

def twistMul (a b : ℤ) : twistingSheaf 𝒜 a ⊗ twistingSheaf 𝒜 b ⟶ twistingSheaf 𝒜 (a + b) :=
  tensorLift (mulPre 𝒜 a b)

lemma twistMul_app (a b : ℤ) (U : (Proj 𝒜).Opens)
    (s : ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 a)).obj (op U))
    (t : ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 b)).obj (op U)) :
    ((preMod (Proj 𝒜)).map (twistMul 𝒜 a b)).app (op U)
        ((tensorToSheaf _ _).app (op U) (s ⊗ₜ t : ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 a) ⊗
          (preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 b)).obj (op U))) =
      mulSec s t := by
  have := congrArg (fun φ => φ.app (op U) (s ⊗ₜ t : ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 a) ⊗
    (preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 b)).obj (op U))) (tensorToSheaf_tensorLift (mulPre 𝒜 a b))
  exact this

lemma mulSec_upow {u : A} (hu : u ∈ 𝒜 1) (a b : ℤ) :
    mulSec (upow 𝒜 hu a) (upow 𝒜 hu b) = upow 𝒜 hu (a + b) :=
  ProjTwist.ext (funext fun x => by
    erw [val_mulSec, val_upow, val_upow, val_upow, twistFrac_mul])

variable (𝒜) in

def oneSections : (twistingSheaf 𝒜 0).sections :=
  ⟨fun U => mkSection (U := U.unop)
      (fun x => ((1 : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj U).1 x).val)
      (isLocallyFraction_val_section (𝒜 := 𝒜) _),
    fun _ => ProjTwist.ext (funext fun _ => rfl)⟩

lemma val_oneSections (U : (Proj 𝒜).Opens) (x : U) :
    val (k := 0) (U := U) ((oneSections 𝒜).val (op U)) x = 1 := by
  change ((1 : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)).1 x).val = 1
  erw [Proj.one_apply, HomogeneousLocalization.val_one]

variable (𝒜) in

def unitToTwistZero : 𝟙_ (Proj 𝒜).Modules ⟶ twistingSheaf 𝒜 0 :=
  (SheafOfModules.unitHomEquiv _).symm (oneSections 𝒜)

lemma unitToTwistZero_one (U : (Proj 𝒜).Opens) {u : A} (hu : u ∈ 𝒜 1)
    (h : U ≤ Proj.basicOpen 𝒜 u) :
    ((preMod (Proj 𝒜)).map (unitToTwistZero 𝒜)).app (op U) (1 : ringOn (Proj 𝒜) U) =
      resM ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 0)) h (upow 𝒜 hu 0) := by
  have e : ((preMod (Proj 𝒜)).map (unitToTwistZero 𝒜)).app (op U) (1 : ringOn (Proj 𝒜) U) =
      (1 : ringOn (Proj 𝒜) U) • (show ((preMod (Proj 𝒜)).obj (twistingSheaf 𝒜 0)).obj (op U) from
        (oneSections 𝒜).val (op U)) := rfl
  rw [e, one_smul]
  apply ProjTwist.ext (k := 0) (U := U)
  funext x
  change val (k := 0) (U := U) ((oneSections 𝒜).val (op U)) x =
    val (k := 0) (U := Proj.basicOpen 𝒜 u) (upow 𝒜 hu 0) ⟨x.1, h x.2⟩
  rw [val_oneSections]
  erw [val_upow]
  simp [twistFrac]

private theorem isIso_twistMul_of_cover (a b : ℤ)
    (hc : ∀ x : Proj 𝒜, ∃ u, u ∈ 𝒜 1 ∧ x ∈ Proj.basicOpen 𝒜 u) : IsIso (twistMul 𝒜 a b) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨u, hu, hx⟩ := hc x
  have e := (twistMul_app a b (Proj.basicOpen 𝒜 u) (upow 𝒜 hu a) (upow 𝒜 hu b)).trans
    (mulSec_upow hu a b)
  refine ⟨Proj.basicOpen 𝒜 u, hx, (tensorToSheaf _ _).app (op (Proj.basicOpen 𝒜 u))
    (upow 𝒜 hu a ⊗ₜ upow 𝒜 hu b :
      ((preMod _).obj (twistingSheaf 𝒜 a) ⊗
        (preMod _).obj (twistingSheaf 𝒜 b)).obj (op (Proj.basicOpen 𝒜 u))),
    ((isBasisOn_upow _ hu a).tmul (isBasisOn_upow _ hu b)).map_of_alt _
      (W_tensorToSheaf _ _), ?_⟩
  rw [e]
  exact isBasisOn_upow _ hu (a + b)

end ProjTwist

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

open ProjTwist

attribute [local instance] MvPolynomial.gradedAlgebra

lemma exists_mem_stdOpen_proj (x : projectiveSpace A n) : ∃ j, x ∈ stdOpen A n j := by
  have hx : x ∈ ⨆ j, stdOpen A n j := by rw [iSup_stdOpen]; trivial
  exact Opens.mem_iSup.1 hx

theorem isInvertibleSheaf_twistingSheaf (k : ℤ) :
    IsInvertibleSheaf (twistingSheaf (grading A n) k) := by
  intro x
  obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj x
  exact ⟨stdOpen A n j, hj, upow (grading A n) (X_mem j) k, isBasisOn_upow _ (X_mem j) k⟩

instance isIso_twistMul (a b : ℤ) : IsIso (twistMul (grading A n) a b) :=
  isIso_twistMul_of_cover a b fun x => by
    obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj x
    exact ⟨_, X_mem j, hj⟩

def twistMulIso (a b : ℤ) :
    twistingSheaf (grading A n) a ⊗ twistingSheaf (grading A n) b ≅
      twistingSheaf (grading A n) (a + b) :=
  asIso (twistMul (grading A n) a b)

instance isIso_unitToTwistZero : IsIso (unitToTwistZero (grading A n)) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj x
  refine ⟨stdOpen A n j, hj, (1 : ringOn _ (stdOpen A n j)), isBasisOn_one _, ?_⟩
  rw [unitToTwistZero_one (stdOpen A n j) (X_mem j) le_rfl]
  exact (isBasisOn_upow _ (X_mem j) 0).restrict le_rfl

instance isNoetherianRing_gradeZero [IsNoetherianRing A] : IsNoetherianRing (grading A n 0) := by
  refine isNoetherianRing_of_surjective A _ (algebraMap A (grading A n 0)) ?_
  rintro ⟨p, hp⟩
  refine ⟨coeff 0 p, Subtype.ext ?_⟩
  rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  by_cases h0 : p = 0
  · subst h0
    simp
  · exact (totalDegree_eq_zero_iff_eq_C.1
      (((mem_homogeneousSubmodule _ _).1 hp).totalDegree h0)).symm

instance isScalarTower_gradeZero :
    IsScalarTower A (grading A n 0) (MvPolynomial (Fin (n + 1)) A) :=
  IsScalarTower.of_algebraMap_eq (R := A) (S := grading A n 0) (A := MvPolynomial (Fin (n + 1)) A)
    fun _ => rfl

instance finiteType_gradeZero :
    Algebra.FiniteType (grading A n 0) (MvPolynomial (Fin (n + 1)) A) :=
  Algebra.FiniteType.of_restrictScalars_finiteType A _ _

instance isLocallyNoetherian [IsNoetherianRing A] : IsLocallyNoetherian (projectiveSpace A n) :=
  LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero (grading A n))

def twistZeroIso : twistingSheaf (grading A n) 0 ≅ 𝟙_ (projectiveSpace A n).Modules :=
  (asIso (unitToTwistZero (grading A n))).symm

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
