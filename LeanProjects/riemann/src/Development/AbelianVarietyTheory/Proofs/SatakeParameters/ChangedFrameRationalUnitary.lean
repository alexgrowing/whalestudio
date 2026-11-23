import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasisStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sigD_eq_star' (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = star x := rfl

theorem cpB_eq_bAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)
  (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La)) =
      (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) := by
  cases j with
  | zero => rfl
  | succ i =>
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (i + 1) La).B.1.submatrix _ _ = _
    simp only [chAt, dif_pos hj]
    rfl

theorem unitary_product_of_hermitian_relations {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J c g B : Matrix (Fin N) (Fin N) E) (hc : cT σ c * c = J) (hg : cT σ g * J * g = J) (hB : cT σ B * J * B = 1) :
    star (c * g * B) * (c * g * B) = 1 := by
  have hs : star (c * g * B) = cT σ (c * g * B) := by
    ext i k
    simp only [cT, Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply, hσ]
  rw [hs, cT_mul, cT_mul]
  calc cT σ B * (cT σ g * cT σ c) * (c * g * B) = cT σ B * (cT σ g * (cT σ c * c) * g) * B := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hc, hg, hB]

theorem changed_frame_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La
  have hB := (GlobalTheory.T.kernelSite_chartBasis_orthonormal_levelIndependent S j hj La.1).1
  have hc := J.pins.crd_orth j hj
  have hg' : (d.gam j hj La)⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj) := inv_mem (d.mem j hj La)
  have hval : (mM d j hj La).1 = (J.A.crd j hj).1 * ((d.gam j hj La)⁻¹).1 * (bAt J j hj La.1).1 := by
    simp only [mM, Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold StdU
    rw [hval]
    exact unitary_product_of_hermitian_relations _ (sigD_eq_star' D) _ _ _ _ hc hg' hB
  · intro v
    rw [GlobalTheory.T.frM_eq_map_crd_mul_gam_inv_mul_basis S d j hj h La v, cpB_eq_bAt J std j hj h La,
      show ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (Fin.cast h) =
        ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (finCongr h) from rfl,
      show (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) = (bAt J j hj La.1).1.submatrix (finCongr h) (Fin.cast h) from rfl,
      Matrix.submatrix_mul_equiv, ← Units.val_mul]
    rfl
  · have hdet : ((d.gam j hj La)⁻¹).1.det * (d.gam j hj La).1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hval, uB, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    linear_combination ((J.A.crd j hj).1.det * (bAt J j hj La.1).1.det) * hdet

end GlobalTheory.TwV.DelA
