import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceField
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA

theorem scal_inv_frame : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → Formalism.L2.G.Pend.cA X Kc j (BOf fd j La) = ι (∏ τ, embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j τ))) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j La n h M hU hF
  have hMu : IsUnit (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det M).isUnit
  have hdet : ∀ v, (fd.frM j La v).det = ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    intro v
    rw [hF v, Matrix.det_submatrix_equiv_self, RingHom.map_det]
    rfl
  have hu : ∀ v, IsUnit (fd.frM j La v).det := fun v => by rw [hdet v]; exact hMu.map (ρ v)
  have hfr : ∀ v, ((frGL fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) = fd.frM j La v := by
    intro v; unfold frGL; rw [dif_pos (hu v)]; rfl
  have hB : ∀ v s, tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det =
      (tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det))⁻¹ := by
    intro v s
    have h1 : ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det * (fd.frM j La v).det = 1 := by
      rw [← hfr v, ← Matrix.det_mul]
      unfold BOf
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 := congrArg (tw X Kc v s) h1
    rw [map_mul, map_one, hdet v] at h2
    exact eq_inv_of_mul_eq_one_left h2
  unfold Formalism.L2.G.Pend.cA
  have hterm : ∀ v s, (tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^
      ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s) =
      ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos ⟨v, s⟩)))) := by
    intro v s
    rw [hB v s, (GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU v s).2, map_zpow₀]
    simp only [wT]
    rw [Equiv.symm_apply_apply]
    split_ifs <;> simp [zpow_neg, inv_inv]
  simp_rw [hterm]
  rw [map_prod]
  exact (Fintype.prod_sigma (fun x => ι (embT D (pos x) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos x)))))).symm.trans
    (Fintype.prod_equiv pos _ _ (fun _ => rfl))

end GlobalTheory.TwV.DelA
