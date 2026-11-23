import Formalism.WeaklyAdmissibleFiltrations.WindowCount

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

private theorem windowCount_Ico_telescope (f : ℤ → ℤ) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, (f a - f (a + 1)) = f m - f k := by
  induction k, hmk using Int.le_induction with
  | base => simp
  | succ k hk ih =>
    have hset : Finset.Ico m (k + 1) = insert k (Finset.Ico m k) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp), ih]
    ring

theorem windowCountAlt : WindowCount := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ τ lo hi hlh
  unfold multV
  exact windowCount_Ico_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) lo hi hlh

end Formalism.WeaklyAdmissibleFiltrations
