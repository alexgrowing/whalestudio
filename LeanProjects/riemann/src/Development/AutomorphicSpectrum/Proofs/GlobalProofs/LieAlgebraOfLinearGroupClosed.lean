import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnit
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem lieOf_isLieSubalgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G),
    (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧
    (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧
    (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧
    (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  intro n G hG
  obtain ⟨𝔤, h𝔤, -⟩ := GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra hG
  have hm : ∀ X, X ∈ HCSS.lieOf G ↔ X ∈ 𝔤 := fun X => (h𝔤 X).symm
  refine ⟨fun X Y hX hY => ?_, fun r X hX => ?_, fun X Y hX hY => ?_, fun k hk X hX => ?_⟩
  · exact (hm _).2 (𝔤.add_mem ((hm X).1 hX) ((hm Y).1 hY))
  · exact (hm _).2 (𝔤.smul_mem r ((hm X).1 hX))
  · exact (hm _).2 ((GlobalTheory.CompanionTheory.LieStable.lieAlg_stable hG 𝔤 h𝔤).2 X ((hm X).1 hX) Y ((hm Y).1 hY))
  · exact (hm _).2 (GlobalTheory.CompanionTheory.LieStable.conj_mem hG h𝔤 hk ((hm X).1 hX))

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
