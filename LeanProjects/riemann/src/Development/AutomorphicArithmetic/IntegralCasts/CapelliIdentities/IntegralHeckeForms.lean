import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.LocalRingCardinality.DataSpaces

attribute [local instance] Submodule.module._proof_1 Formalism.MainNotions.S.lf._proof_1 Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul :
    ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E}
    (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS T)
    (M : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.WbQ D F0)),
    Submodule.span D.host.E (↑M : Set (Formalism.MainNotions.S.WbQ D F0)) = ⊤ →
      ∀ (m : Formalism.MainNotions.S.WbQ D F0),
        ∃ (k : ℕ),
          k ≠ (0 : ℕ) ∧
            (↑k : NumberField.RingOfIntegers D.host.E) • m ∈
              M := by
  intro D T F0 M h m
  simp only [Nat.cast_smul_eq_nsmul]
  refine Submodule.span_induction (p := fun x _ => ∃ k : ℕ, k ≠ 0 ∧ k • x ∈ M)
    (fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h ▸ Submodule.mem_top : m ∈ Submodule.span D.host.E (M : Set _))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    exact ⟨a * b, mul_ne_zero ha hb, by
      rw [smul_add, mul_nsmul' y, mul_nsmul x]; exact M.add_mem (nsmul_mem hx b) (nsmul_mem hy a)⟩
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨b, s, hb, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic c)).exists_nsmul_eq (NumberField.RingOfIntegers D.host.E)
    exact ⟨b * a, mul_ne_zero hb ha, by
      rw [mul_smul, smul_comm a c, ← smul_assoc, hs, algebraMap_smul]; exact M.smul_mem s hx⟩
