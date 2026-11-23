import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.muT_det_ratA : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) ∧ ∀ k (hk : k ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) = ∏ τ, TaylorLogMetric.embT D τ γ.1.det ^ e τ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj
  obtain ⟨e, he, hz⟩ := S.law.mu_rat j hj
  refine ⟨e, he, fun k hk γ hγ => ?_⟩
  have hu := ((GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S) k hk).2 γ hγ
  have key : Matrix.GeneralLinearGroup.det (ratA D.host.F γ) =
      Formalism.L2.DIV.ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det γ) := by
    ext
    simp [ratA, Formalism.UG.bc, Formalism.L2.DIV.ratId, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [key]
  have h2 := hz (Matrix.GeneralLinearGroup.det γ) (by simpa using hu.2)
  simpa using h2
