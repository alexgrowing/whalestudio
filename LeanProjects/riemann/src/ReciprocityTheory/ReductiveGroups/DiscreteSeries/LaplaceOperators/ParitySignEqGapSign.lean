import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.ParEpsQOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapStep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def NVStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
    GapLap (parEps k r) (parLam k r v b) h → BesselAll (parEps k r) (parLam k r v b) u

theorem nv_of (hI : Base.StepIBaseStatement) (hS : StepStatement) (hIS : S0.IntSStatement)
    (hDD : DecDerivStatement) : NVStatement := by
  intro k r u v b h hk hHC hIL hHalf hLow hGap
  have hp := parEps_pOf k r hk
  have hq := parEps_qOf k r hk
  have hSG : StepGap (parEps k r) r h := by
    have := gapLap_stepGap _ (parEps k r) (parLam k r v b) h (by rw [hp]; omega) (by rw [hq]; omega) hGap
    rwa [hq, Nat.add_sub_cancel] at this
  obtain ⟨t₀, ht⟩ := hI k r u v b hk hHC hIL hHalf
  exact TransportInt.transport_of hIS hDD hk hGap
    (walkStep hIS hS k r u v b h t₀ hk hHC hIL hHalf hLow hSG (ht t₀ le_rfl))

end ReciprocityTheory.ChartRestriction.DS.Lap
