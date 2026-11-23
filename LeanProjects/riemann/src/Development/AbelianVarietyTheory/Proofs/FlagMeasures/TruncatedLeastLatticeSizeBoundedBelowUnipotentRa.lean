import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzPropertiesStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem one_le_rank_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    1 ≤ I.n := by
  by_contra h
  have h0 : I.n = 0 := by omega
  haveI : IsEmpty (Fin I.n) := by rw [h0]; infer_instance
  exact hW.1 (Subsingleton.elim _ _)

theorem exists_pos_le_tau1_mul_of_mem_NA_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA)
    (hW : I.IsIsot W) : ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  obtain ⟨hpos, hcont, hinv, -⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I (one_le_rank_of_isIsot I W hW)
  obtain ⟨-, -, -, -, Cp, hCp, -, hcov⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  have hc : Continuous fun y : I.GA => tau1 I (y * x) := hcont.comp (continuous_id.mul continuous_const)
  have key : ∀ m ∈ I.NA W, ∃ y ∈ Cp, tau1 I (m * x) = tau1 I (y * x) := by
    intro m hm
    obtain ⟨γ, hγ, hy⟩ := hcov m hm
    refine ⟨γ⁻¹ * m, hy, ?_⟩
    rw [← hinv γ hγ.1 (γ⁻¹ * m * x)]
    congr 1
    group
  rcases Cp.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun m hm => ?_⟩
    obtain ⟨y, hy, -⟩ := key m hm
    rw [he] at hy
    exact hy.elim
  · obtain ⟨y₀, -, hmin⟩ := hCp.exists_isMinOn hne hc.continuousOn
    refine ⟨tau1 I (y₀ * x), hpos _, fun m hm => ?_⟩
    obtain ⟨y, hy, e⟩ := key m hm
    rw [e]
    exact hmin hy

end GlobalTheory.Dec
