import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckTens

open scoped Matrix.Norms.Elementwise

theorem okTens : OKTens := by
  intro k r F F' hF hF'
  refine ⟨?_, ?_, ?_, ?_⟩
  · show F.ρ 1 ⊗ₖ F'.ρ 1 = 1
    rw [hF.one, hF'.one, Matrix.one_kronecker_one]
  · intro g hg h hh
    show F.ρ (g * h) ⊗ₖ F'.ρ (g * h) = (F.ρ g ⊗ₖ F'.ρ g) * (F.ρ h ⊗ₖ F'.ρ h)
    rw [hF.mul g hg h hh, hF'.mul g hg h hh, Matrix.mul_kronecker_mul]
  · rintro ⟨c, c'⟩ ⟨d, d'⟩ g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hF.smooth c d g₀ hg₀
    obtain ⟨U', f', hU', hgU', hf', hfe'⟩ := hF'.smooth c' d' g₀ hg₀
    refine ⟨U ∩ U', fun x => f x * f' x, hU.inter hU', ⟨hgU, hgU'⟩,
      (hf.mono Set.inter_subset_left).mul (hf'.mono Set.inter_subset_right), ?_⟩
    intro g hg hin
    have h1 := hfe g hg.1 hin
    have h2 := hfe' g hg.2 hin
    show F.ρ g c d * F'.ρ g c' d' = f g * f' g
    simp only at h1 h2
    rw [h1, h2]
  · obtain ⟨C, hC⟩ := hF.growth
    obtain ⟨C', hC'⟩ := hF'.growth
    refine ⟨C * C', ?_⟩
    rintro g hg ⟨c, c'⟩ ⟨d, d'⟩
    show ‖F.ρ g c d * F'.ρ g c' d'‖ ≤ C * C' * Formalism.FourierDecayAlt.B.gN g ^ (F.deg + F'.deg)
    have h1 := hC g hg c d
    have h2 := hC' g hg c' d'
    rw [norm_mul, pow_add]
    calc _ ≤ (C * Formalism.FourierDecayAlt.B.gN g ^ F.deg) * (C' * Formalism.FourierDecayAlt.B.gN g ^ F'.deg) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.ZuckTens
