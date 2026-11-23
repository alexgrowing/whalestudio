import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem isNef_pull_of_isProjOver : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  intro k _ X Y p s hp N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (s ≫ p)
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨pull_isLB hN.isLB s, fun C hC => ?_⟩
  rcases interNumRed_pull_curve p s C hC with h | ⟨C', hC', d, hd⟩
  · rw [h N hN.isLB]
  · rw [hd N hN.isLB]
    exact mul_nonneg (Int.natCast_nonneg d) (hN.nonneg C' hC')

end GlobalTheory.NumPull
