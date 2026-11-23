import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictStructureSheafAffineBasisPull1BijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenPreimageEqBaseChangeSqZeroAugmentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorSectionsHomBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalBijectiveCoefficientsPull1BijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpensPreimageBaseChangeIsBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairPreimageBaseChangeFstIsBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCoefficientComparisonCommPairPullbackStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffineHom_of_isPullback {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback hp.flip inferInstance

theorem res_bijective (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] : Function.Bijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 :=
  have H := GlobalTheory.T.affineOpensPreimage_baseChange_isBasis X₀ X₁ pr (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp)
  GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ X₁ s₁ _ (preAff pr) H.1 H.2

theorem tens_bijective {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) [IsAffineHom pr] :
    Function.Bijective (tensCoef hp.w).pull1 := by
  exact GlobalTheory.T.natural_bijective_coefficients_pull1_bijective R₁ _ _ _ _ (tensCoef hp.w).naturality (tensCoef hp.w).smul fun U ↦ GlobalTheory.T.baseChangeTensorSectionsHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop _

def trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CatCoh.H1 (OAff s₁) ≃+ CatCoh.H1 (ext R₁ (OAff s₀)) :=
  haveI := isAffineHom_of_isPullback hp
  (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 (res_bijective q hq hp)).trans
    (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).symm

theorem tens_trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] (c : CatCoh.H1 (OAff s₁)) :
    (tensCoef hp.w).pull1 (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) = (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c :=
  (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).apply_symm_apply _

section Compat

variable {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr] [IsAffineHom pr']
  {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁} (e : f₁ ≫ pr = pr' ≫ f₀)

def pullBC (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preAff pr ⋙ OAff s₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((pairBC pr pr' e).obj p)
  naturality a b := (pairPull h₁).naturality ((pairBC pr pr' e).map a) b
  smul p r b := (pairPull h₁).smul ((pairBC pr pr' e).obj p) r b

def resBC : CoefMap (RingHom.id R₁) (preAff pr' ⋙ OAff t₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end Compat

end GlobalTheory.Obs.BC

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem extendedCoefficients_pullback_compat (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0)
    {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀}
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀)
    (c : CatCoh.H1 (OAff s₁)) (c' : CatCoh.H1 (OAff t₁))
    (H : IsExtendedPullbackDegOne R₁ h₀ (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) :
    IsPullO h₁ c c' := by
  haveI := isAffineHom_of_isPullback hp
  haveI := isAffineHom_of_isPullback hp'
  have kd := tens_trEquiv q hq hp c
  have kd' := tens_trEquiv q hq hp' c'
  let Φ := CoefMap.restrict (OPair f₁ t₁) (pairBC pr pr' e)
  have inj : Function.Injective Φ.pull1 := by
    intro x x' hx
    obtain ⟨y, rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x
    obtain ⟨y', rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x'
    have HH := GlobalTheory.T.affinePairPreimage_baseChange_fst_isBasis X₀ X₁ Y₀ Y₁ pr pr' f₀ f₁ e (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp')
    have B := GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ Y₁ t₁ _ (pairBC pr pr' e ⋙ pairFst f₁) HH.1 HH.2
    have k : ∀ z, Φ.pull1 ((pairRes f₁ t₁).pull1 z) =
        (CoefMap.restrict (OAff t₁) (pairBC pr pr' e ⋙ pairFst f₁)).pull1 z := by
      intro z; obtain ⟨z, rfl⟩ := H1.mk_surjective _ z; rfl
    rw [k, k] at hx
    rw [B.1 hx]
  have k1 : Φ.pull1 ((pairPull h₁).pull1 c) = (tensPair hp'.w e).pull1 ((extMap R₁ (pairPull h₀)).pull1
      (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c)) := by
    have a1 : Φ.pull1 ((pairPull h₁).pull1 c) =
        (pullBC e h₁).pull1 ((CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c) := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [a1, ← kd, ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp.w).comp (pullBC e h₁))
      ((extMap R₁ (pairPull h₀)).comp (tensPair hp'.w e)) (𝟙 (pairSnd f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff s₀)) _ b)).trans ?_
    exact GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback R₀ R₁ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' hp.w hp'.w f₀ f₁ h₀ h₁ e p b
  have k2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') = (tensPair hp'.w e).pull1 ((extMap R₁ (pairRes f₀ t₀)).pull1
      (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) := by
    have a2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') =
        (resBC e).pull1 ((CoefMap.restrict (OAff t₁) (preAff pr')).pull1 c') := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c'; rfl
    rw [a2, ← kd', ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp'.w).comp (resBC e))
      ((extMap R₁ (pairRes f₀ t₀)).comp (tensPair hp'.w e)) (𝟙 (pairFst f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff t₀)) _ b)).trans ?_
    have hc : coefHom (pairRes f₀ t₀) p = AlgHom.id R₀ _ := AlgHom.ext fun _ ↦ rfl
    change (tensPair hp'.w e).α p (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = _
    rw [hc]
    exact congrArg ((tensPair hp'.w e).α p) (DFunLike.congr_fun Algebra.TensorProduct.map_id b)
  apply inj
  unfold IsExtendedPullbackDegOne at H
  rw [k1, k2, H]

end GlobalTheory.Obs.BC

theorem GlobalTheory.Obs.BC.extO1 : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' :=
  fun _ _ _ _ _ q hq ↦ ⟨GlobalTheory.Obs.BC.trEquiv q hq, fun _ _ _ _ _ hp _ _ _ _ _ hp' _ _ h₀ h₁ e c c' H ↦
    GlobalTheory.Obs.BC.extendedCoefficients_pullback_compat q hq hp hp' h₀ h₁ e c c' H⟩
