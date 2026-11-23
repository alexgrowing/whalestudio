import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem toLE_eq_mulVec (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ x = γ.1 *ᵥ x := rfl

theorem toStdCo_stdG_eq (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap =
      ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap ∘ₗ Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (toLE co).surjective x
  have h1 : (co⁻¹ : GL (Fin N) E).1 * co.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (toLE (1 : GL (Fin N) E)) = LinearEquiv.refl E _ := by
    ext z : 1
    simp [toLE_eq_mulVec]
  have h3 : Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) (toLE co y) = toLE co (toLE γ y) := by
    rw [Matrix.toLin'_apply, toLE_eq_mulVec, toLE_eq_mulVec, toLE_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (co⁻¹).1, h1, Matrix.mul_one]
  rw [LinearMap.comp_apply, h3]
  simp [toStdCo, stdG, h2]

theorem det_toStdCo_stdG (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap).det =
      γ.1.det * (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by
  rw [toStdCo_stdG_eq, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.det_mul, Matrix.det_mul,
    Matrix.det_mul]
  have h : (co.1).det * ((co⁻¹ : GL (Fin N) E).1).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  calc _ = γ.1.det * ((co.1).det * ((co⁻¹ : GL (Fin N) E).1).det) *
        (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by ring
    _ = _ := by rw [h, mul_one]

theorem det_cT (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E) : (cT σ M).det = σ M.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_norm_of_UJ (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = G) (hγ : γ ∈ UJ σ G) : σ γ.1.det * γ.1.det = 1 := by
  have hγ' : cT σ γ.1 * G * γ.1 = G := hγ
  have hG : G.det ≠ 0 := by
    rw [← hco, Matrix.det_mul, det_cT]
    have hc : (co.1).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp co.isUnit |>.ne_zero
    exact mul_ne_zero ((map_ne_zero σ).mpr hc) hc
  have h := congrArg Matrix.det hγ'
  rw [Matrix.det_mul, Matrix.det_mul, det_cT] at h
  have h' : (σ γ.1.det * γ.1.det - 1) * G.det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hG

end Gen

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem gMat_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ k (hk : k ≤ D.R.m), (gMat J k hk 1).det * D.host.conj (gMat J k hk 1).det = 1 ∧
      ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk),
        (gMat J k hk γ).det = γ.1.det * (gMat J k hk 1).det ∧ γ.1.det * D.host.conj γ.1.det = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S k hk
  have hs : ∀ y : D.host.E, (sigD D : D.host.E →+* D.host.E) y = D.host.conj y := fun y =>
    Formalism.BasicNotions.bridge_star_holds D.R D.host y
  have hco := J.pins.crd_orth k hk
  refine ⟨?_, fun γ hγ => ⟨?_, ?_⟩⟩
  · have h := GlobalTheory.TwV.cT_mul_self_toStdCo_stdG (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) 1 hco
      (Subgroup.one_mem _)
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, det_cT, Matrix.det_one, hs] at h2
    rw [mul_comm]
    exact h2
  · exact det_toStdCo_stdG _ _ _ _
  · have h := det_norm_of_UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) γ hco hγ
    rw [hs, mul_comm] at h
    exact h

end GlobalTheory.TwV.DelB

end
