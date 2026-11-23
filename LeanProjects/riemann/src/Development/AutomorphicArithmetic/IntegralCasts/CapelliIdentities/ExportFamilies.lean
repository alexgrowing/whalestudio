import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

theorem UpperTheory.Reformulated.B.ExportFamilies.K_repr :
    ∀ (D : Formalism.L2.Ker.Car),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) D.host.sqd)]
    exact hx
  refine Algebra.adjoin_induction (p := fun x _ => ∃ p q : ℚ, x = (p : D.host.E) + q * D.host.sqd)
    (fun y hy => ⟨0, 1, by simpa using hy⟩) (fun r => ⟨r, 0, by simp⟩) ?_ ?_ hx'
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      push_cast; linear_combination ((b : D.host.E) * e) * hs⟩
