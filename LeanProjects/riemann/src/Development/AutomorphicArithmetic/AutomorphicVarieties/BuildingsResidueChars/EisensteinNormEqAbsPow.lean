import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
open UpperTheory.V.Sd.Eis NumberField GlobalTheory.Mem.Chr.CharModel

theorem UpperTheory.eisenstein_norm_eq_abs_pow :
    UpperTheory.V.Sd.Eis.AbsPow := by
  intro F _ _ _ s
  have H := absChar_isAbsPow (F := F) s
  refine ⟨⟨absHom F s, (absChar F s).2⟩, fun y hy => ?_, fun w => ⟨H.1 w, ?_⟩⟩
  · change Complex.exp (s * logNorm F (UpperTheory.V.TR.infId F y)) = _
    have h1 : finPart F (UpperTheory.V.TR.infId F y) = 1 := by
      apply Units.ext
      change (UpperTheory.V.TR.infId F y).val.2 = 1
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).2 = 1
      change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) - 0 + 0 = 1
      simp
    have h2 : (infPart F (UpperTheory.V.TR.infId F y)).val = UpperTheory.V.TR.infEq F y.val := by
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).1 = _
      change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F y.val = _
      simp
    have h3 : ∀ w : InfinitePlace F, ‖UpperTheory.V.TR.infEq F y.val w‖ = y.val w := fun w => by
      have := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.isometry.dist_eq (y.val w) 0
      have e0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 = 0 :=
        map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      rw [e0, dist_zero_right, dist_zero_right, Real.norm_of_nonneg (hy w).le] at this
      exact this
    rw [logNorm, h1, logFin_one, sub_zero, logInf, h2]
    simp only [h3, InfinitePlace.mult, IsTotallyReal.isReal, if_true, Nat.cast_one, one_mul]
    rw [← Real.log_prod (fun w _ => (hy w).ne'), Real.rpow_def_of_pos (Finset.prod_pos fun w _ => hy w),
      Complex.ofReal_exp, Complex.ofReal_mul, mul_comm]
  · refine (H.2.1 w).trans ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
