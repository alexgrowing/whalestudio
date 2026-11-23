import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSpreadThetaLevelAbelianSchemeAwayStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_complete_dvr_point (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (f : R) (hf : f ≠ 0) :
    ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V))
      (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V),
      (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ y f ≠ 0 := by
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.exists_prime_natCast_mem_of_finiteType_int 𝔪
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, y, hy, hyf⟩ := GlobalTheory.exists_padic_point 𝔪 hpm hf
  exact ⟨integralClosure ℤ_[p] L, L, inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure L, GlobalTheory.DiscEval.finite_residueField_integralClosure L,
    inferInstance, charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective, inferInstance,
    inferInstance, y, hy, hyf⟩

theorem exists_obj_over_complete_dvr : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  intro L1 L2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ _ β v t 𝔪 h𝔪 hth hsh hpr
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨f, hf, t', ψ, -, -, hth', hsh', hpr'⟩ :=
    GlobalTheory.T.exists_spread_theta_level_abelian_scheme_away L1 L2 o g N' J b Mat κ w w' R K β v t hth hsh hpr
  obtain ⟨V, F, i1, i2, i3, i4, i5, i6, i7, i8, i9, y, hy, hyf⟩ :=
    exists_complete_dvr_point R 𝔪 h𝔪 f hf
  have hu : IsUnit (((algebraMap V F).comp y) f) :=
    isUnit_iff_ne_zero.mpr fun h => hyf (IsFractionRing.injective V F (h.trans (map_zero _).symm))
  let φ : Localization.Away f →+* F := IsLocalization.Away.lift f hu
  have hφ : φ.comp (algebraMap R (Localization.Away f)) = (algebraMap V F).comp y :=
    IsLocalization.Away.lift_comp f hu
  have hsq : spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ spMap β =
      spMap (algebraMap V F) ≫ spMap (y.comp β) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← RingHom.comp_assoc, hφ, RingHom.comp_assoc]
  obtain ⟨tF, hm⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b _ _ _ _ (spMap φ) t' hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g (N' ^ 2) J b Mat κ w w' _ _ _ _ _ t' tF hm
  refine ⟨V, F, i1, i2, i3, i4, i5, i6, i7, i8, i9, y, tF, hy, h1 hsh', h2 hpr', ?_⟩
  have h3 := GlobalTheory.T.hasThetaConstants_ring_baseChange L2 o g N' J b _ _ t' _ _ φ _ _ hth'
  refine (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ t' _ _ tF _ F _ _ hm).mpr ?_
  rw [Category.id_comp]
  rw [Category.comp_id] at h3
  have e : (fun a => algebraMap V F (y (v a))) =
      fun a => φ (algebraMap R (Localization.Away f) (v a)) :=
    funext fun a => (RingHom.congr_fun hφ (v a)).symm
  rw [e]
  exact h3

end GlobalTheory.ZM
