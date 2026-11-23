import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameFinitePartMemCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSignStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTranslateThetaCoordinateOfRealPartLawStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRealForm

theorem vacuum_real_law : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D) (δ : ℂ), GlobalTheory.FockCompare.Chart W.θ σ → Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pS (.top t j)).rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pT (.top t j)).rank), ∀ Y, Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x (GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ) Y = GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ Y := by
  intro D T L sc G W U N σ δ hσ hcrv hδ t j hj f hf x hx Y
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.T.torusLattice_standard_points_scaled_embedding δ x hx
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top j)).1 * (G.V (.top j)).gram * (N.fr (.top j)).1 = 1 :=
    N.fr_on (.top j) (show j ≤ D.R.m by omega)
  have hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top (j + 1))).1 * (G.V (.top (j + 1))).gram *
      (N.fr (.top (j + 1))).1 = 1 := N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)
  have hlat := GlobalTheory.T.orthonormalFrame_finitePart_mem_completedLattice (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS M hM
  obtain ⟨k, hk, heig⟩ := GlobalTheory.T.heisenbergOperator_finitePart_latticeVacuum_sign W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (colLat (N.fr (.top j))) (colLat (N.fr (.top (j + 1))))
    hf.1 (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hS) (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hT) f hf.2.lat _ hlat
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hσ hf.1 hf.2.theta _ heig
  rw [GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing, neg_zero, AddChar.map_zero_eq_one, one_mul] at hlaw
  have hU := GlobalTheory.T.torusTranslate_thetaCoordinate_of_realPart_law σ (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M f _ hlaw Y
  have hal := GlobalTheory.T.torusSemicharacter_eq_neg_one_pow_traceExponent (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M k hk
  show Formalism.MainNotions.TaylorLogMetric.al D _ _ * Formalism.MainNotions.TaylorLogMetric.U D _ _ (thY σ (G.V (.top j)) (G.V (.top (j + 1))) (fun τ => (N.fr (.top j)).1.map (tauE D τ))
    (fun τ => (N.fr (.top (j + 1))).1.map (tauE D τ)) f δ) Y = _
  rw [hU, ← mul_assoc, hal, one_mul]
  rfl

end GlobalTheory.VacRealForm
