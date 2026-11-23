import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.GlueSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Walk
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem parEps_qOf (k r : ℕ) (hk : 1 ≤ k) : qOf (parEps k r) = r + 1 :=
  noncompactCount_parabolicSign k r hk

theorem parEps_pOf (k r : ℕ) (hk : 1 ≤ k) : pOf (parEps k r) = k + r := by
  have h := compactCount_parabolicSign k r hk
  rw [show parEps k r = Formalism.MainNotions.CayleySignature.eps48 k r from rfl, h]
  omega

theorem walkStep : WalkStepStatement := by
  intro hIS hStep k r u v b h t hk hHC hI hH hL hG hB
  exact walk k r u v b h t (fun lam => BesselNZ (parEps k r) lam u) hk hHC hI hH hL
    (hStep hIS k r (parEps k r) u h hG (parEps_pOf k r hk) (parEps_qOf k r hk)) hB

end ReciprocityTheory.ChartRestriction.DS.Lap
