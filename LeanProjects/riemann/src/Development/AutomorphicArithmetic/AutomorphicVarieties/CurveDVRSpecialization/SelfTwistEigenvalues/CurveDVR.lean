import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CurveOverSeries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CompleteDVRExt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CurveDVRPrecompleteFinite
open Polynomial Matrix

open IsLocalRing in
private theorem curveDVR_prec_finite {O M : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M :=
  _root_.UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite I

private theorem curveDVR_prec_cofinal {R : Type} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem curveDVR_complete {R R' : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    curveDVR_prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (curveDVR_prec_finite _))
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

open IsLocalRing in
private theorem exists_dvr_quotient_of_complete_local {A R : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
    [Algebra A R] [FaithfulSMul A R] [Module.Finite A R] :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (f : R →+* B),
        IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧ Finite (IsLocalRing.ResidueField B) ∧
        Function.Injective f ∧ IsLocalHom f ∧ f.Finite := by
  letI : Algebra (FractionRing A) (FractionRing R) := FractionRing.liftAlgebra A (FractionRing R)
  haveI : IsScalarTower A (FractionRing A) (FractionRing R) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing R)
  haveI : FiniteDimensional (FractionRing A) (FractionRing R) := inferInstance
  obtain ⟨hfin, hdvr⟩ :=
    UpperTheory.V.Pr.T.completeDVRExt (A := A) (K := FractionRing A) (L := FractionRing R)
  have hmem : ∀ r : R, algebraMap R (FractionRing R) r ∈ integralClosure A (FractionRing R) :=
    fun r => (Algebra.IsIntegral.isIntegral (R := A) r).algebraMap
  let f : R →+* integralClosure A (FractionRing R) :=
    (algebraMap R (FractionRing R)).codRestrict (integralClosure A (FractionRing R)) hmem
  have hinj : Function.Injective f := fun x y h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  letI : Algebra R (integralClosure A (FractionRing R)) := f.toAlgebra
  haveI : IsScalarTower A R (integralClosure A (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq fun x => Subtype.ext
      (IsScalarTower.algebraMap_apply A R (FractionRing R) x)
  haveI hF : Module.Finite R (integralClosure A (FractionRing R)) :=
    Module.Finite.of_restrictScalars_finite A R _
  have hf : f.Finite := hF
  haveI hl : IsLocalHom f := hf.to_isIntegral.isLocalHom hinj
  haveI : IsLocalHom (algebraMap R (integralClosure A (FractionRing R))) := hl
  refine ⟨integralClosure A (FractionRing R), inferInstance, inferInstance, hdvr, f,
    curveDVR_complete (R := R), ?_, hinj, hl, hf⟩
  exact Module.finite_of_finite (ResidueField R)

theorem UpperTheory.V.Pr.T.curveDVR :
    ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
      (p : ℕ) [Fact p.Prime] [CharP R p], ringKrullDim R = 1 →
      ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : R →+* A),
        IsAdicComplete (IsLocalRing.maximalIdeal A) A ∧ Finite (IsLocalRing.ResidueField A) ∧
        Function.Injective f ∧ IsLocalHom f ∧ f.Finite := by
  intro R _ _ _ _ _ _ p _ _ hdim
  obtain ⟨g, hinj, -, hfin⟩ := UpperTheory.V.Pr.T.curveOverSeries (R := R) p hdim
  letI : Algebra (PowerSeries (ZMod p)) R := g.toAlgebra
  haveI : FaithfulSMul (PowerSeries (ZMod p)) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Module.Finite (PowerSeries (ZMod p)) R := hfin
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries (ZMod p))) (PowerSeries (ZMod p)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  exact exists_dvr_quotient_of_complete_local (A := PowerSeries (ZMod p))
