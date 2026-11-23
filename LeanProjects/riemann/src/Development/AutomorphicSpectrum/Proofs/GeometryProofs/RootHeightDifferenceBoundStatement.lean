import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_height_difference_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N), Close M R i u c → ArchBetween M R i u t lam s lo hi → ∀ (L : Type) [Field L] [NumberField L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈ Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht <;> assumption)
