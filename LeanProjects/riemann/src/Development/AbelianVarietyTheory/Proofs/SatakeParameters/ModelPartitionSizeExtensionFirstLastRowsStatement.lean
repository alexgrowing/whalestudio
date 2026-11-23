import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRows
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelPartition_size_extension_firstLast_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  first | exact @GlobalTheory.TwV.DelA.size_first_last_rows | exact GlobalTheory.TwV.DelA.size_first_last_rows | (intros; apply GlobalTheory.TwV.DelA.size_first_last_rows <;> assumption)
