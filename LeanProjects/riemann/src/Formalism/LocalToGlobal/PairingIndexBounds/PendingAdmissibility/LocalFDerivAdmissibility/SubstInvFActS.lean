import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.AdmTwoPendantIff

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend
open scoped Kronecker Matrix

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem latAt_smul (X : Sys p) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup) (v : X.Pl) :
    X.latAt v j ((X.Lv.lev j c).smul γ L) =
      (X.latAt v j L).map ((Matrix.mulVecLin (gamAt X j c γ v : Matrix _ _ (X.G.P.Qq v))).restrictScalars (X.G.P.W v)) := by
  cases j <;> rfl

theorem map_map_inv {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (A : GL (Fin k) Qq)
    (M : Submodule W (Fin k → Qq)) :
    (M.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)).map
      ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = M := by
  rw [← Submodule.map_comp]
  have hid : ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W).comp
      ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp [Matrix.mulVec_mulVec]
  rw [hid, Submodule.map_id]

def frmMove (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') : Frm X j (La.1, L0) La' where
  g := fun v => (gamAt X j La.1 γ v)⁻¹ * φ.g v
  g' := φ.g'
  hg := fun v => by
    have h1 := φ.hg v
    rw [h, latAt_smul] at h1
    show X.latAt v j L0 = _
    rw [Units.val_mul, ← colSpan_mul, ← h1, map_map_inv]
  hg' := φ.hg'

def frmBack (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ0 : Frm X j (La.1, L0) La') : Frm X j La La' where
  g := fun v => gamAt X j La.1 γ v * φ0.g v
  g' := φ0.g'
  hg := fun v => by
    have h1 := φ0.hg v
    change X.latAt v j L0 = _ at h1
    rw [h, latAt_smul, h1, colSpan_mul, Units.val_mul]
  hg' := φ0.hg'

theorem frmMove_frmBack (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup}
    (γ : (X.Lv.lev j La.1).Γ) (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ0 : Frm X j (La.1, L0) La') :
    frmMove X γ h (frmBack X γ h φ0) = φ0 := by
  cases φ0 with
  | mk g g' hg hg' =>
    unfold frmMove frmBack
    congr 1
    funext v
    exact inv_mul_cancel_left _ _

theorem subst_invF_actS (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
    {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') (z : X.ZA j) :
    MvPowerSeries.subst (invF Kc φ) (actS X Kc j (gamAt X j La.1 γ) z) = invF Kc (frmMove X γ h φ) z := by
  have hI : MvPowerSeries.HasSubst (invF Kc φ) := by apply hasSubst_invF
  rcases z with ⟨v, s, a, b⟩
  have hQ : Qi Kc (frmMove X γ h φ) v s = Qi Kc φ v s := by
    unfold Qi
    rfl
  have hm : ∀ A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v),
      mAt X Kc j v s (A * B) = mAt X Kc j v s A * mAt X Kc j v s B := by
    intro A B
    unfold mAt
    rw [Matrix.map_mul, Matrix.submatrix_mul_equiv]
  simp only [actS, invF]
  simp_rw [← MvPowerSeries.smul_eq_C_mul]
  rw [← MvPowerSeries.coe_substAlgHom hI, map_sum]
  simp_rw [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hI]
  simp only [invF]
  simp_rw [← MvPowerSeries.smul_eq_C_mul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ab' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rcases ab' with ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, hQ]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  unfold Pi
  try dsimp only [frmMove]
  by_cases ho : IsOddPos s
  · simp only [if_pos ho]
    rw [Units.val_mul, hm, Matrix.mul_apply]
  · simp only [if_neg ho, Matrix.transpose_apply]
    rw [mul_inv_rev, inv_inv, Units.val_mul, hm, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem thA_SA (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
    {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') (f : MvPowerSeries (X.ZA j) Kc) :
    thA Kc φ (SA X Kc j (gamAt X j La.1 γ) f) = thA Kc (frmMove X γ h φ) f := by
  have hI : MvPowerSeries.HasSubst (invF Kc φ) := by apply hasSubst_invF
  have hA : MvPowerSeries.HasSubst (actS X Kc j (gamAt X j La.1 γ)) := by apply hasSubst_actS
  unfold thA SA
  rw [MvPowerSeries.subst_comp_subst_apply hA hI]
  congr 1
  funext z
  exact subst_invF_actS X Kc γ h φ z

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
