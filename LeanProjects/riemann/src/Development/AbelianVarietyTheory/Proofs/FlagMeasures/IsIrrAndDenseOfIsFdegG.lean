import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem IsFdegG.dense_span_orbit {G : Type} [MeasurableSpace G] {μ : Measure G} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : G → (H →L[ℂ] H)} {d : ℝ} (h : IsFdegG μ σ d)
    (w : H) (hw : w ≠ 0) : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  obtain ⟨hd, hint⟩ := h
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu

  have hzero : ∀ g, ⟪u, σ g w⟫_ℂ = 0 := fun g =>
    inner_eq_zero_symm.mp (hu (σ g w) (Submodule.subset_span ⟨g, rfl⟩))

  have key := (hint w u w u).2
  have hfun : (fun g => ⟪u, σ g w⟫_ℂ * star ⟪u, σ g w⟫_ℂ) = fun _ => (0 : ℂ) := by
    funext g
    simp [hzero g]
  rw [hfun, integral_zero] at key
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw' : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw
  have huu : ⟪u, u⟫_ℂ = 0 := by
    rcases div_eq_zero_iff.mp key.symm with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hw'
    · exact absurd h1 hd'
  exact inner_self_eq_zero.mp huu

theorem isIrr_and_dense_of_isFdegG : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)) (d : ℝ), IsFdegG μ σ d → IsIrr σ ∧ ∀ w : H, w ≠ 0 → Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  intro G _ μ H _ _ _ σ d h
  refine ⟨?_, fun w hw => IsFdegG.dense_span_orbit h w hw⟩
  intro S hS hinv
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwS, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

    have hsub : Submodule.span ℂ (Set.range fun g => σ g w) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hinv g w hwS
    have hcl : closure ((Submodule.span ℂ (Set.range fun g => σ g w) : Submodule ℂ H) : Set H) ⊆ (S : Set H) :=
      closure_minimal (fun y hy => hsub hy) hS
    rw [Submodule.eq_top_iff']
    intro x
    exact hcl (by rw [(IsFdegG.dense_span_orbit h w hw).closure_eq]; exact Set.mem_univ x)

end GlobalTheory.Dec
