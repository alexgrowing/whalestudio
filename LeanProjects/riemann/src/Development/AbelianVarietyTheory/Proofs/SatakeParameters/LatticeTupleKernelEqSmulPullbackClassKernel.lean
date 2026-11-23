import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelicStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicCharactersAtDetRationalIsometryRepLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem reV_pull_submatrix {D : D7} (T : TaylorLogMetric.Tor D) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    (e : Matrix (Fin N) (Fin N) D.host.E) (e' : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    reV ha hb (TaylorLogMetric.pull D T e e' G) =
      TaylorLogMetric.pull D T (e.submatrix (Fin.cast ha) (Fin.cast ha)) (e'.submatrix (Fin.cast hb) (Fin.cast hb)) (reV ha hb G) := by
  subst ha hb
  rfl

theorem pullAt_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  intro D _ _ _ _ _ _ _ _ u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa' z
  have hj1 : j + 1 ≤ D.R.m := hj
  have hj0 : j ≤ D.R.m := Nat.le_of_succ_le hj1
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  rw [GlobalTheory.T.kernelFunction_latticeTuple_pair_eq_adelic S hD j hj1 (hr j) (hr (j + 1)) La La' hLa hLa']
  have hV := GlobalTheory.T.thetaKernelFunction_adelicPoints_eq_pullback_classKernel J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj1 (clsAt X H j La.1 La.2)
    (clsAt X H (j + 1) La'.1 La'.2) (J.pt std j _ La) (J.pt std (j + 1) hj1 La') (d.gam j _ La) (d.mem j _ La)
    (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap j _ La) (d.kap (j + 1) hj1 La') (d.eq j _ La hLa) (d.eq _ _ La' hLa')
  have hN := (GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j + 1) hj1 (clsAt X H (j + 1) La'.1 La'.2)
    (J.pt std (j + 1) hj1 La') (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap (j + 1) hj1 La') (d.eq _ _ La' hLa')).2.2
  have e1 : d.eM j La = (gMat J j hj0 (d.gam j hj0 La)).submatrix (Fin.cast (hr j)) (Fin.cast (hr j)) := by
    unfold Dec.eM; rw [dif_pos ⟨hj0, hr j⟩]
  have e2 : d.eM (j + 1) La' = (gMat J (j + 1) hj1 (d.gam (j + 1) hj1 La')).submatrix (Fin.cast (hr (j + 1))) (Fin.cast (hr (j + 1))) := by
    unfold Dec.eM; rw [dif_pos ⟨hj1, hr (j + 1)⟩]
  have e3 : thCl (X := sysS H X std) t u μ (clsAt X H) j La La' =
      reV (hr j) (hr (j + 1)) ((t.rd u μ).Th t.seam t.amb j (clsAt X H j La.1 La.2) (clsAt X H (j + 1) La'.1 La'.2)) := by
    unfold thCl; rw [dif_pos ⟨hr j, hr (j + 1)⟩]
  have e4 : d.sP S j La La' = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap j hj0 La).1) * d.chi (j + 1) hj1 La' /
      (S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap (j + 1) hj1 La').1) * d.chi j hj0 La) := by
    unfold Dec.sP; rw [dif_pos hj1]
  rw [e1, e2, e3, e4, ← reV_pull_submatrix]
  have key : ∀ a b c e k p : ℂ, c ≠ 0 → e ≠ 0 → c * e * k = a * b * p → k = a * b / (c * e) * p := by
    intro a b c e k p hc he h
    field_simp
    linear_combination h
  exact key _ _ _ _ _ _ hN (Units.ne_zero _)
    (hV (fun τ i k => z τ (Fin.cast (hr (j + 1)).symm i) (Fin.cast (hr j).symm k)))

end GlobalTheory.TwV.DelB
