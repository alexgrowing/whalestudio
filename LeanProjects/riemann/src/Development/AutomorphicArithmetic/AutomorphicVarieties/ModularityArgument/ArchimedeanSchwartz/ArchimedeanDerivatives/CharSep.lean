import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
open IsDedekindDomain Neutral.B1 GlobalTheory.ModelChar GlobalTheory.CuspRep Formalism.L2.Host

namespace UpperTheory.V.Z.Inf.H.Phase

private def ex (r : ℝ) : ℂˣ := Circle.toUnits (Circle.exp r)

private theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  simp [ex, Circle.exp_add]

private theorem ex_zero : ex 0 = 1 := by simp [ex]

variable {K : Type} [Field K] [NumberField K]

private def modU (t : ℝ) : ℂˣ →* ℂˣ where
  toFun z := ex (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp [ex_zero]
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      ex_add]

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

variable (K) in

private def cmp (w : InfinitePlace K) : Ideles K →* ℂˣ :=
  (Units.map (Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toRingHom.toMonoidHom).comp
    (Units.map (infEv w))

variable (K) in

private def ar (n : InfinitePlace K → ℤ) : Ideles K →* ℂˣ where
  toFun a := ∏ w, argU (cmp K w a) ^ n w
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow, Finset.prod_mul_distrib]

variable (K) in

private def md (t : InfinitePlace K → ℝ) : Ideles K →* ℂˣ where
  toFun a := ∏ w, modU (t w) (cmp K w a)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

end UpperTheory.V.Z.Inf.H.Phase

namespace UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf.H.Phase

end UpperTheory.V.Z.Inf
