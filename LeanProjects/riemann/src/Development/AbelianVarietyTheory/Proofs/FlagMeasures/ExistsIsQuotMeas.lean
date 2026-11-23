import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgQuot

theorem isMatGroup_GG (k r : ℕ) : PI.IsMatGroup (GG k r) := by

  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨⟨_, _, h, (mul_comm _ _).trans h⟩, rfl⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ _ hH
  refine ⟨?_, h1, hmul, fun a ha => ⟨(hinv a ha).2, Matrix.mul_nonsing_inv a (hinv a ha).1⟩⟩

  show IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exists_isQuotMeas : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r S μG μS hS hG hSμ hU
  obtain ⟨hSG, hcl, h1, hmul, hinv⟩ := hS

  have hSm : PI.IsMatGroup S :=
    ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ((isMatGroup_GG k r).2.2.2 a (hSG ha)).2⟩⟩

  exact GlobalTheory.QuotWeil.exists_isQuotM (2 * r + k + 1) (GG k r) S μG μS (isMatGroup_GG k r) hSm hSG hG hSμ hU.1

end GlobalTheory.SgQuot
