import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharDeterminantIdealUnitarySmulSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitaryStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem detId_stdL_heq (D : D7) {n n' : ℕ} (h : n = n') {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} (hL : HEq L L') :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) L = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n') L' := by
  subst h
  cases hL
  rfl

theorem chi_detId_kerN : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det)⁻¹ * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ∧ (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det) ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hK, -⟩ := hD j hj La hLa
  have hlat := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice J.A J.dtU J.a J.pins J.tie j hj (clsAt X H j La.1 La.2) (J.pt std j hj La)
    (d.gam j hj La) (d.mem j hj La) (d.kap j hj La) (d.eq j hj La hLa)
  have hU : gMat J j hj (d.gam j hj La) * star (gMat J j hj (d.gam j hj La)) = 1 :=
    GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary J.A J.dtU J.a J.pins J.tie j hj (d.gam j hj La) (d.mem j hj La)
  have hcl := GlobalTheory.T.determinantIdealCharacter_classLattice_eq J.A J.dtU J.a J.pins J.tie J.rel J.base j hj (clsAt X H j La.1 La.2)
  have hmv := GlobalTheory.T.char_determinantIdeal_unitary_smul_selfDual D t.χ t.χ_ok ((t.O u μ).lat j (clsAt X H j La.1 La.2)) (gMat J j hj (d.gam j hj La)) hU
  rw [t.O_lat] at hmv
  have h1 := detId_stdL_heq D hr hK
  refine ⟨?_, ?_⟩
  · rw [h1]
    have : latK D.sp (gramN D j hj) J.a (J.pt std j hj La).1 ((J.St j hj).K (J.chart std j hj La)).lev.Lb =
        SDLat.smulLat (gMat J j hj (d.gam j hj La)) (t.seam.lat ((t.rd u μ).N j (clsAt X H j La.1 La.2))) := hlat
    rw [this, hmv, hcl]
  · have hdet : (gMat J j hj (d.gam j hj La)).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hU
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero (TaylorLogMetric.embT D τ)).mpr hdet

end GlobalTheory.TwV.DelB
