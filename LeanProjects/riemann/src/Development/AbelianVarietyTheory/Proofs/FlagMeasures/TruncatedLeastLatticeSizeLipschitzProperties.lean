import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.TauLipschitz

theorem trunc_pos (I : AutInst) (hn : 1 ≤ I.n) (x : I.GA) : 0 < tau1 I x :=
  lt_min (by norm_num) ((GlobalTheory.CountSteps.steps I x 1 one_pos).2.2.2.2.2.2.2.2 hn).1

theorem log_trunc_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    Real.log (tau1 I x) - dSum I g.1 / I.f ≤ Real.log (tau1 I (x * g)) := by
  have h := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x g hg
  have hx := trunc_pos I hn x
  have h2 := Real.log_le_log (mul_pos hx (Real.exp_pos _)) h
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  unfold dSum
  linarith

theorem dSum_inv (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) : dSum I (g⁻¹).1 = dSum I g.1 := by
  unfold dSum
  refine Finset.sum_congr rfl fun v _ => ?_
  exact ((GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 (g.1 v) (g.1 v) hn).2.1

theorem tauLip : TauLip := by
  intro I hn
  refine ⟨trunc_pos I hn, (GlobalTheory.LeastVar.least_variation_continuity I hn).2.2, ?_, ?_⟩
  · rintro a ⟨γ, h1, h2, h3⟩ x
    unfold tau1
    rw [(GlobalTheory.PointEquivariance.equivariance I x γ a h1 h2 h3).2.2.1]
  · intro x g hg
    obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
    have hg' : (g⁻¹).2 ∈ I.Kset := by
      rw [← hK] at hg ⊢
      exact K.inv_mem hg
    have h1 := log_trunc_le I hn x g hg
    have h2 := log_trunc_le I hn (x * g) g⁻¹ hg'
    rw [mul_inv_cancel_right, dSum_inv I hn] at h2
    rw [abs_le]
    constructor <;> linarith

end GlobalTheory.TauLipschitz
