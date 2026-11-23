import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecomposition
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.snc_boundary_ample_decomposition : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  first | exact @_root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier | exact _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier | (intros; apply _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier <;> assumption)
