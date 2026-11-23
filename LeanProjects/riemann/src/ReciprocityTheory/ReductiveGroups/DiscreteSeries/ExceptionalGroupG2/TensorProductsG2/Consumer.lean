import Formalism.PeriodIntegrals.ZuckTensor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Sandwich
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

open MeasureTheory

def ZuckG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
      ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1)

def ZuckDualG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
      ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1)

theorem zuckG : ZuckG := by
  intro n ε μ H _ _ _ σ hμ hd h hG hth
  by_cases hq : 1 ≤ S7.q0 ε
  · exact cns_zuck_nc hq hμ hd hG hth
  · have h0 : S7.q0 ε = 0 := by omega
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      simp only [S7.q0] at h0
      omega
    exact cns_zuck_cpt hpq hμ hd

theorem zuckDualG : ZuckDualG := by
  intro n ε μ H _ _ _ σ hμ hd h hG hth
  by_cases hq : 1 ≤ S7.q0 ε
  · exact cns_zuckd_nc hq hμ hd hG hth
  · have h0 : S7.q0 ε = 0 := by omega
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      simp only [S7.q0] at h0
      omega
    exact cns_zuckd_cpt hpq hμ hd

end ReciprocityTheory.ChartRestriction.DS.G2
