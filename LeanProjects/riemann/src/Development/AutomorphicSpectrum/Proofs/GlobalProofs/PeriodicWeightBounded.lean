import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd

theorem periodic_mul {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (i : Fin r) (k : ℕ)
    (m : Fin r → ℕ) : v (m + (Pi.single i (k * l) : Fin r → ℕ)) = v m := by
  induction k with
  | zero => simp
  | succ k ih => rw [add_mul, one_mul, Pi.single_add, ← add_assoc, hv, ih]

theorem reduce_on {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (s : Finset (Fin r))
    (m : Fin r → ℕ) : v m = v (fun i => if i ∈ s then m i % l else m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [ih]
    have hfun : (fun i => if i ∈ s then m i % l else m i) =
        (fun i => if i ∈ insert a s then m i % l else m i) +
          (Pi.single a (m a / l * l) : Fin r → ℕ) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha, Nat.mod_add_div']
      · simp [hj, Pi.single_eq_of_ne hj]
    rw [hfun, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.periodic_mul hv]

theorem bddW_of_periodic : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l →
    (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  intro r l v hl hv
  refine ⟨∑ f : Fin r → Fin l, |((v fun i => (f i : ℕ) : ℚ) : ℝ)|, fun m => ?_⟩
  have hm : v m = v fun i => ((⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l) : ℕ) := by
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.reduce_on hv Finset.univ m
  rw [hm]
  exact Finset.single_le_sum (f := fun f : Fin r → Fin l => |((v fun i => (f i : ℕ) : ℚ) : ℝ)|)
    (fun f _ => abs_nonneg _) (Finset.mem_univ fun i => (⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l))

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd
