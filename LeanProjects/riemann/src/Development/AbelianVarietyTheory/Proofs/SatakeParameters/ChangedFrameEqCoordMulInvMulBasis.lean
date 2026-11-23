import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecompositionUnitaryMulStarEqOneStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

section SlopeTestRemainingChoices
variable {E : Type} [Field E]
theorem toMatrix'_stdCo_reindex {n N : ℕ} (h : N = n) (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) :
    LinearMap.toMatrix' (stdCo σ (G.reindex (finCongr h) (finCongr h))).toLinearMap =
      (LinearMap.toMatrix' (stdCo σ G).toLinearMap).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  subst h
  simp

theorem toMatrix'_linEquiv_symm_mul {n : ℕ} (e : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  simp

theorem toMatrix'_toLE_eq {n : ℕ} (g : GL (Fin n) E) : LinearMap.toMatrix' (toLE g).toLinearMap = (g : Matrix (Fin n) (Fin n) E) := by
  simp only [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  exact LinearMap.toMatrix'_toLin' (g : Matrix (Fin n) (Fin n) E)

theorem toMatrix'_toLE_symm_eq {n : ℕ} (g : GL (Fin n) E) :
    LinearMap.toMatrix' (toLE g).symm.toLinearMap = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  rw [Matrix.coe_units_inv, ← toMatrix'_toLE_eq]
  exact (Matrix.inv_eq_left_inv (toMatrix'_linEquiv_symm_mul _)).symm
end SlopeTestRemainingChoices

section Site
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)

theorem Joint.cp_iw_eq_rho (j : ℕ) (La : (sysS H X std).Lt j) (v : (sysS H X std).Pl) : (J.cp std).iw j La v = J.rho std v := by
  cases j with
  | zero => rfl
  | succ i =>
    simp only [Joint.cp, cpAt, chAt]
    split_ifs with hi
    · exact J.iw i hi _ v
    · rfl

theorem Joint.stdCo_cpJ_mat (j : ℕ) (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap).submatrix (Fin.cast hr) (Fin.cast hr) := by
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    exact toMatrix'_stdCo_reindex _ _ _
  | succ i =>
    simp only [Joint.cp, cpAt, chAt, dif_pos hj]
    exact toMatrix'_stdCo_reindex _ _ _

theorem gMat_eq_mul (j : ℕ) (hj : j ≤ D.R.m) (γ : GL (Fin (D.R.N j)) D.host.E) :
    gMat J j hj γ = LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      ((γ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) * (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) := by
  unfold gMat toStdCo stdG
  simp only [LinearEquiv.coe_trans, LinearMap.toMatrix'_comp]
  rw [toMatrix'_toLE_eq, toMatrix'_toLE_symm_eq, mul_assoc (_ * _), ← mul_assoc (LinearMap.toMatrix' _), toMatrix'_linEquiv_symm_mul, one_mul,
    mul_assoc]
end Site

theorem changedFrame_eq_coord_mul_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj hr La v
  have hU' : star (d.eM j La) * d.eM j La = 1 := mul_eq_one_comm.mp (GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d j La)
  have hE : d.eM j La = (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
        (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E))).submatrix
        (finCongr hr) (finCongr hr) := by
    rw [Dec.eM, dif_pos ⟨hj, hr⟩, gMat_eq_mul]
    rfl
  have hC : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix
        (finCongr hr) (finCongr hr)) := by
    rw [Joint.stdCo_cpJ_mat J std j hj hr La, hE, Matrix.submatrix_mul_equiv]
    have h1 : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
        (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
          (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) *
        (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E)) =
        LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap := by
      rw [Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
    rw [h1]
    rfl
  show (star (d.eM j La)).map (J.rho std v) * ((((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap) *
      ((J.cp std).B j La).1).map ((J.cp std).iw j La v)).submatrix (finCongr ((J.cp std).hk j La)) (finCongr ((J.cp std).hk j La))) = _
  rw [Joint.cp_iw_eq_rho, hC]
  change (star (d.eM j La)).map (J.rho std v) * (d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v) =
    ((((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v)
  rw [← Matrix.map_mul, ← mul_assoc, ← mul_assoc, hU', one_mul]

end GlobalTheory.TwV.DelB

end
