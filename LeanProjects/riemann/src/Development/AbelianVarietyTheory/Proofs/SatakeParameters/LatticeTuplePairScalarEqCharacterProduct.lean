import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterDetIdealKernelLatticeLatticeTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentityStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

set_option maxHeartbeats 1000000 in

theorem scalAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.ScalAt S j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa'
  obtain ⟨hmm, ht, hN, -⟩ := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hj0 : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hdt0 := (hD j hj0 La hLa).2.2.2
  have hdt1 := (hD (j+1) hj1 La' hLa').2.2.2
  have e0 := d.eq j hj0 La hLa
  have e1 := d.eq (j+1) hj1 La' hLa'
  have M0 := GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj j hj0 (clsAt X H j La.1 La.2) (J.pt std j hj0 La) (d.gam j hj0 La) (d.mem j hj0 La) (d.kap j hj0 La) e0
  have M1 := GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j+1) hj1 (clsAt X H (j+1) La'.1 La'.2) (J.pt std (j+1) hj1 La') (d.gam (j+1) hj1 La') (d.mem (j+1) hj1 La') (d.kap (j+1) hj1 La') e1
  have C0 := GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple S hD d j hj0 La hLa
  have C1 := GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple S hD d (j+1) hj1 La' hLa'
  have eN0 : (((sysS H X std).Pj j).m + 1) / 2 = D.R.N j / 2 := by rw [hN]
  have eN1 : (((sysS H X std).Pj (j + 1)).m + 1) / 2 = D.R.N (j + 1) / 2 := by rw [hN]
  have R0 : ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ)⁻¹ *
        ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ (-(((D.R.N (j + 1) / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf]
  have R1 : ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) *
        ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ ((((D.R.N j / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf']
  simp only [Dec.sC, Dec.sP, Dec.uS, Dec.uT, scal0, Base.chiFac, dif_pos hj1, dif_pos hj0]
  rw [R0, R1, hdt0, hdt1, M0.1, M1.1, C0.1, C1.1, eN0, eN1, ht]
  exact GlobalTheory.T.pullback_contraction_scalars_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cTw D j) (cTw D (j + 1)) (Units.ne_zero _) (Units.ne_zero _) M0.2.1 M1.2.1 M0.2.2 M1.2.2
    (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) C0.2 C1.2

end GlobalTheory.TwV.DelB
