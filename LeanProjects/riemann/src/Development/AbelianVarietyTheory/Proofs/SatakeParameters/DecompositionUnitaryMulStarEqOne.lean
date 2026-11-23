import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitaryStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem Dec.eM_mul_star : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j La, d.eM j La * star (d.eM j La) = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j La
  unfold Dec.eM
  split_ifs with h
  · have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary J.A J.dtU J.a J.pins J.tie j h.1 (d.gam j h.1 La) (d.mem j h.1 La)
    have hc : (Fin.cast h.2 : Fin (((sysS H X std).Pj j).m + 1) → Fin (D.R.N j)) = ⇑(finCongr h.2) := rfl
    rw [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose]
    have hu' : gMat J j h.1 (d.gam j h.1 La) * star (gMat J j h.1 (d.gam j h.1 La)) = 1 := hu
    rw [hu', Matrix.submatrix_one_equiv]
  · simp

end GlobalTheory.TwV.DelB
