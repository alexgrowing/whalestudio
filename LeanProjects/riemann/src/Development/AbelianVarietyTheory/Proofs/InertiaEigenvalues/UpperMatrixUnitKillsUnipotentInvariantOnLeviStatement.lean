import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperMatrixUnitKillsUnipotentInvariantOnLevi
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperMatrixUnit_kills_unipotentInvariant_on_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (ψ : Sm E N), (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) → ∀ (τ : E →+* ℂ) (p q : Fin N), blk (stdBlocks n h) p < blk (stdBlocks n h) q → ∀ m, (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  first | exact @GlobalTheory.UnipKill.eop_leviEmb_eq_zero | exact GlobalTheory.UnipKill.eop_leviEmb_eq_zero | (intros; apply GlobalTheory.UnipKill.eop_leviEmb_eq_zero <;> assumption)
