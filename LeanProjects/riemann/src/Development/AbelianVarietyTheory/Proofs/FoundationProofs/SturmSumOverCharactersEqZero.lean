import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlane
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sturm_sum_coef_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ,
    (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  classical
  intro k L N hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  choose f hf using fun ε => modularForm_gammaOne_of_MF k L N ε (a ε) hL hN (ha ε)
  have hc : ∀ ε n, (qExpansion 1 (f ε)).coeff n = a ε n := by
    intro ε n
    have := coef_qs (a ε) (ha ε).1 n
    unfold coef at this
    rw [← this, hf]
  have hsum : ∀ (s : Finset (DirichletCharacter ℂ N)) (n : ℕ),
      (qExpansion 1 ⇑(∑ ε ∈ s, f ε)).coeff n = ∑ ε ∈ s, a ε n := by
    intro s n
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero, map_zero]
    | insert e s he ih =>
      rw [Finset.sum_insert he, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ, map_add, ih, hc, Finset.sum_insert he]
  have h0 : ∑ ε, f ε = 0 := hm _ fun n hn => by
    rw [hsum]
    simpa [Finset.sum_apply] using hz n hn
  funext n
  have := hsum Finset.univ n
  rw [h0] at this
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero] at this
  rw [Finset.sum_apply, ← this]
  rfl

example : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ, (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := sturm_sum_coef_zero

end GlobalTheory.EisM
