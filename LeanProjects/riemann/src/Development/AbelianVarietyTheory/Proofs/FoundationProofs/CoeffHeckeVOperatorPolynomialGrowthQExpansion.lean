import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem Vo_polyB_qs : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a →
    PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  intro l a hl ha
  refine ⟨?_, ?_⟩
  · obtain ⟨C, A, h⟩ := ha
    have hC : 0 ≤ C := by
      have := h 0
      simp at this
      exact le_trans (norm_nonneg _) this
    refine ⟨C, A, fun n => ?_⟩
    unfold Vo
    split_ifs with hd
    · refine (h (n / l)).trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self n l
    · simp only [norm_zero]; positivity
  · intro τ σ hσ
    unfold qs
    have hinj : Function.Injective (fun m : ℕ => l * m) :=
      fun x y hxy => Nat.eq_of_mul_eq_mul_left hl hxy
    have hsupp : Function.support (fun n : ℕ => Vo l a n * cexp (2 * π * Complex.I * n * τ)) ⊆
        Set.range (fun m : ℕ => l * m) := by
      intro n hn
      by_contra hr
      apply hn
      have : ¬ l ∣ n := by
        rintro ⟨m, rfl⟩
        exact hr ⟨m, rfl⟩
      simp [Vo, this]
    rw [← hinj.tsum_eq hsupp]
    congr 1
    ext m
    have hl' : l ≠ 0 := hl.ne'
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl, hσ]
    congr 2
    push_cast
    ring

end GlobalTheory.EisM
