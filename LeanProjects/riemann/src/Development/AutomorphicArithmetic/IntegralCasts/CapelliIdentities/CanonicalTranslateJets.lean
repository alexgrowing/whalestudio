import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

theorem UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr :
    ∀ (D : Formalism.BasicNotions.D7),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ ({D.host.sqd} : Set D.host.E) :=
    (IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun y _ => Algebra.IsAlgebraic.isAlgebraic y).le hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by simpa using hy⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * D.host.d, a * e + b * c, by push_cast; linear_combination (b * e : D.host.E) * hs⟩
