import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStableStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem To_MF : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L →
    MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  intro k L N q ε a hk hNL hq hqL ha
  have h1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨hP, hqs⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) a hk hq.pos h1 ha.1
  refine ⟨hP, ?_⟩
  rw [hqs]
  refine GlobalTheory.T.heckeCharacterSlashSum_invariant_of_stable k L L N ε (DT L q) (Option (Fin q)) (repT q) (qs a) hk hNL hNL ?_ ?_
    (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL) ha.2
  · rintro δ ⟨hdet, hL⟩
    refine ⟨by rw [hdet]; exact_mod_cast hq.pos, ?_⟩
    exact (Int.natCast_dvd_natCast.mpr hNL).trans hL
  · rintro δ ⟨hdet, hL⟩ γ hγ
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_mul, hdet]
      simp
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hL _) (dvd_mul_of_dvd_right hγ _)

end GlobalTheory.EisM
