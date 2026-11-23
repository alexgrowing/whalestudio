import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def MeanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M →
    ∀ τ : D.what₂.Tau, meanLogOm D (tor0 D cc δ).abelian₂ M τ = logOmVal D

def MeanPeriod : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    MeanPeriodAt D cc δ

theorem logOmVal_eq (D : D7) :
    logOmVal D = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / D.host.rdE) - logDerivativeAtOne D := by
  have h : Real.pi / D.host.v = 2 * Real.pi / D.host.rdE := by
    unfold Host.v
    rw [div_div_eq_mul_div, mul_comm]
  unfold logOmVal
  rw [h]

example (D : D7) : IsCurveIdeal D ⊤ := by
  refine ⟨top_ne_bot, ?_⟩
  simp [Ideal.absNorm_top]

example (D : D7) (cc : Ideal (𝓞 D.host.K)) : ∃ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

end GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms
