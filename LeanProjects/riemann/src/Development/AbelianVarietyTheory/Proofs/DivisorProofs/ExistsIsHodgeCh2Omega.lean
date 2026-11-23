import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemann
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCInfNormOfIsHodge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDegEq
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

theorem GlobalTheory.PPAS.exists_isHodge_ch2Omega : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ P : PPAS X, ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsHodge h ∧ h.IsCInfNorm ∧ h.IsCh2Deg (P.ch2Omega p) ∧ h.first_chern_integral = P.degOmega p := by
  intro hA k _ X p _ hreg hX P
  obtain ⟨h, H⟩ := GlobalTheory.PPAS.exists_isDualRiemann k X p P Real.pi Real.pi_pos
  have hn := GlobalTheory.PPAS.isCInfNorm_of_isHodge P H
  obtain ⟨a, ha⟩ := hn.exists_isCh2Deg hA hreg hX
  refine ⟨h, H, hn, ?_, ?_⟩
  · rw [GlobalTheory.PPAS.IsHodge.ch2Omega_eq (P := P) H ha]; exact ha
  · exact (GlobalTheory.ChernDegree.first_chern_integral_eq_degree k X p hX _ _ h hn).2
