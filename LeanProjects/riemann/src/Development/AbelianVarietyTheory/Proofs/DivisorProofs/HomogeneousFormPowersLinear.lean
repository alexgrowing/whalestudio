import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.IntLinPow

theorem homog_eq_sum_pow_intLin : ∀ (D : ℕ) (F : MvPolynomial (Fin 5) ℝ), F.IsHomogeneous D →
    ∃ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D := by
  intro D F hF
  have hmem : F ∈ Submodule.span ℝ (Set.range fun n : Fin 5 → ℤ => lin (fun i => (n i : ℝ)) ^ D) := by
    by_contra hnot
    obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill : ∀ n : Fin 5 → ℤ, φ (lin (fun i => (n i : ℝ)) ^ D) = 0 := by
      intro n
      have hm : lin (fun i => (n i : ℝ)) ^ D ∈ Submodule.span ℝ
          (Set.range fun n : Fin 5 → ℤ => lin (fun i => (n i : ℝ)) ^ D) := Submodule.subset_span ⟨n, rfl⟩
      have h2 : φ (lin (fun i => (n i : ℝ)) ^ D) ∈ (Submodule.span ℝ
          (Set.range fun n : Fin 5 → ℤ => lin (fun i => (n i : ℝ)) ^ D)).map φ := Submodule.mem_map_of_mem hm
      rw [hφ] at h2
      exact (Submodule.mem_bot ℝ).mp h2
    have hP : PowLinSpan.polOf φ D = 0 := by
      refine eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ D)
        (fun _ => (Finset.range (D + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
      · intro x
        rw [Finset.card_image_of_injective _ Nat.cast_injective]
        simpa using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ D x)
      · intro v hv
        have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
          intro i
          obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
          exact ⟨k, hk⟩
        choose k hk using hv'
        rw [PowLinSpan.eval_polOf]
        have h := hkill (fun i => (k i : ℤ))
        have he : (∑ x, C (v x) * X x : MvPolynomial (Fin 5) ℝ) = lin (fun i => (((k i : ℤ)) : ℝ)) := by
          simp only [lin, Int.cast_natCast, hk]
        rw [he]
        exact h
    exact hφF (PowLinSpan.homog_kill φ D hP F hF)
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c.support, c, ?_⟩
  rw [← hc, Finsupp.sum]

end GlobalTheory.IntLinPow
