import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.UnipotentRadicalHaar

theorem eq_smul_of_twoSided {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : B.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • ν := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν.finite_compact K hK⟩
  obtain ⟨c, -, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique hU hμ
    (ν := ν) ⟨inferInstance, hν.ne_zero, hν.conc, hν.left⟩
  exact ⟨c, c1, e⟩

theorem unimodular_normal : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsRightInvM (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsFiniteMeasure μW ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Nset k r) μN ∧ (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, h * m * h⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) ∧ ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h * Matrix.of x * h⁻¹) i j : Formalism.QuantumDeterminants.Mt k r)) = μN := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨νW, hνW⟩ := P.weyl_haar_exists k r z hz hT
  obtain ⟨νN, hνN⟩ := P.unipotent_haar_exists k r
  obtain ⟨a, a1, ea⟩ := eq_smul_of_twoSided (P.B2x3.closedW k r z) hW hνW
  obtain ⟨b, -, eb⟩ := eq_smul_of_twoSided (P.B2x2.closedN k r) hN hνN
  refine ⟨fun s hs => ?_, ⟨?_⟩, fun s hs => ?_,
    fun h hh m hm => (Formalism.QuantumDeterminants.uWNormal k r z hz h hh m hm).1, fun h hh => ?_⟩
  · rw [ea, Measure.map_smul]
    exact congrArg (a • ·) (hνW.right s hs)
  · have hK : IsCompact (Formalism.QuantumDeterminants.UWset k r z) := P.weyl_subgroup_compact k r z hz hT
    have h1 : νW (Formalism.QuantumDeterminants.UWset k r z) < ⊤ := hνW.finite_compact _ hK
    have h2 : νW Set.univ ≤ νW (Formalism.QuantumDeterminants.UWset k r z) + νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    have h3 : νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ = 0 := hνW.conc
    rw [h3, add_zero] at h2
    rw [ea, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top a1.lt_top (h2.trans_lt h1)
  · rw [eb, Measure.map_smul]
    exact congrArg (b • ·) (hνN.right s hs)
  · rw [eb, Measure.map_smul]
    exact congrArg (b • ·) (P.b2_conjInvRaw_proof k r z νN hz hT hνN h hh)

end GlobalTheory.UnipotentRadicalHaar
