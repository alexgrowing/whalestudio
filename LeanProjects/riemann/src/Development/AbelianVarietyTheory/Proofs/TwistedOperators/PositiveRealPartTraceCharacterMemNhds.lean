import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PosNhdsChar

theorem posNhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  intro D ψ hψ n ρ L x
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hlin : ∀ c : AE D, Continuous fun a : AE D => c * a := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF D.host.F) c)
  have htr : Continuous fun a : AE D => Algebra.trace (AF D.host.F) (AE D) a :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hψc : Continuous ψ := hψ.1.1
  have hcont : Continuous fun z : Mx D n ρ => star (psiE ψ (upSum (L ⬝ (z - x)))) := by
    refine continuous_star.comp (hψc.comp (htr.comp ?_))
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · simp only [Matrix.mul_apply, Matrix.sub_apply]
      refine continuous_finset_sum _ fun k _ => ?_
      have hk : Continuous fun z : Mx D n ρ => z k j - x k j := by
        simp only [sub_eq_add_neg]
        exact (continuous_id.matrix_elem k j).add continuous_const
      exact (hlin (L i k)).comp hk
    · exact continuous_const
  refine IsOpen.mem_nhds (isOpen_lt continuous_const (Complex.continuous_re.comp hcont)) ?_
  show (0:ℝ) < (star (psiE ψ (upSum (L ⬝ (x - x))))).re
  simp [upSum, psiE]

end GlobalTheory.PosNhdsChar
