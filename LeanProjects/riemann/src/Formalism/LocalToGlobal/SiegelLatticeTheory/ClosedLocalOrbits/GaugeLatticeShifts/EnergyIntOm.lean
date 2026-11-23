import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.EnergyIntOm

variable {D : D7} (X : HidaSetting D)

def dsc (lam : ℂ) (sc : ℝ) (a : Fin (D.R.rS + 1)) : ℂ := (lam * (sc : ℂ)) ^ (D.R.rS - a.val)

theorem dsc_ne {lam : ℂ} (hl : lam ≠ 0) {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (D.R.rS + 1)) : dsc (D := D) lam sc a ≠ 0 := by
  unfold dsc
  exact pow_ne_zero _ (mul_ne_zero hl (by exact_mod_cast hsc))

theorem dsc_last (lam : ℂ) (sc : ℝ) : dsc (D := D) lam sc (Fin.last D.R.rS) = 1 := by
  unfold dsc
  simp

theorem q_fvec {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u : D.what₂.Word) (a : Fin (D.R.rS + 1)) :
    Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) a = dsc (D := D) lam sc a • frm X u sc v a := by
  obtain ⟨-, h2, -, h4⟩ := hQ
  have hsc' : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc
  induction a using Fin.lastCases with
  | last =>
    have hl : ¬ (Fin.last D.R.rS).val < D.R.rS := by simp
    unfold Formalism.QuantumDeterminants.fvec
    rw [dif_neg hl, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, dsc_last, one_smul]
    unfold frm famSc fam
    simp [Fin.snoc_last]
  | cast b =>
    have hb : (Fin.castSucc b).val < D.R.rS := b.isLt
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    rw [dif_pos hb]
    have hbb : (⟨(Fin.castSucc b).val, hb⟩ : Fin D.R.rS) = b := Fin.ext rfl
    rw [hbb, (h4 b b rfl).1]
    unfold dsc frm famSc fam
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    rw [smul_smul, mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsc'), mul_one]

theorem zhat_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : sc ≠ 0) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) (trG Q Qi (γ v)) a b =
      star (dsc (D := D) lam sc a) * dsc (D := D) lam sc b * ZX X u u' sc γ v a b := by
  obtain ⟨-, h2, h3, -⟩ := id hQ
  have ea := q_fvec X hQ hsc u a
  have eb := q_fvec X hQ hsc u' b
  unfold ZX Formalism.QuantumDeterminants.Zhat trG
  unfold Formalism.L2.SG.RealObj.Zhat
  beta_reduce
  unfold Formalism.QuantumDeterminants.herm Formalism.L2.SG.HidaSetting.hJ
  rw [← h3]
  have hm : Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q * (Qi * uMat (γ v) * Q) =
      Qᴴ * (Formalism.REAL.Jm (X.B.I.ε v) * (uMat (γ v) * Q)) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ea,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_smul, smul_eq_mul]
  ring

theorem dmin_diag (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (d : Fin (D.R.rS + 1) → ℂ)
    (h : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g = Matrix.diagonal d) (l : Fin (D.R.rS + 2)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Formalism.QuantumDeterminants.Dmin
  rw [h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem mem_om {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (c : Cinf X) (hc : c ∈ Good X u u') (γ : X.B.I.Ginf)
    (hγ : HasDiag X u u' sc c γ) :
    trG Q Qi (γ v) ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  have hc' : ∀ w, (∀ l, c w l ≠ 0) ∧ 0 < Gv (Tw u) (Tw u') (Matrix.diagonal (c w)) := hc
  have hγ' : ∀ w, ZX X u u' sc γ w = Matrix.diagonal (c w) := hγ
  obtain ⟨dd, hdd⟩ : ∃ dd : Fin (D.R.rS + 1) → ℂ,
      dd = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * c v a := ⟨_, rfl⟩
  have hdiag : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi (γ v)) = Matrix.diagonal dd := by
    ext a b
    rw [zhat_tr X hQ hsc0 u u' γ a b, hγ' v, hdd]
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hdsc : ∀ a, star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a ≠ 0 := fun a =>
    mul_ne_zero (star_ne_zero.mpr (dsc_ne (D := D) hl hsc0 a)) (dsc_ne (D := D) hl hsc0 a)
  have hd0 : ∀ a, dd a ≠ 0 := by
    intro a
    rw [hdd]
    exact mul_ne_zero (hdsc a) ((hc' v).1 a)
  have hDmin := fun l => dmin_diag (D := D) _ _ _ _ hdiag l
  have hTz : ∀ w : D.what₂.Word, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR w)) = Tw w := by
    intro w
    have hQz : Q *ᵥ (Qi *ᵥ rv X.B.I v (X.zR w)) = rv X.B.I v (X.zR w) := by
      rw [Matrix.mulVec_mulVec, hQ.2.1, Matrix.one_mulVec]
    have hJ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v w
    unfold Formalism.L2.SG.HidaSetting.hJ at hJ
    unfold Formalism.QuantumDeterminants.Tz Formalism.QuantumDeterminants.herm
    rw [← hQ.2.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQz, hJ]
    simp
  unfold Formalism.FourierDecayAlt.JF.Om
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 (γ v), ?_⟩
  rw [Formalism.FourierDecayAlt.Q.OmPlus, Set.mem_ofPred_eq]
  refine ⟨fun l _ => ?_, ?_⟩
  · rw [hDmin l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · have hlast : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) (Fin.last (D.R.rS + 1)) =
        (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := by
      rw [hDmin]
      have h : ∏ i : Fin (D.R.rS + 1), dd i =
          (∏ i : Fin D.R.rS, dd (Fin.castSucc i)) * dd (Fin.last D.R.rS) := Fin.prod_univ_castSucc _
      exact h
    have hr : Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
        (trG Q Qi (γ v)) ⟨D.R.rS, by omega⟩ = ∏ i : Fin D.R.rS, dd (Fin.castSucc i) := by
      rw [hDmin]
      rfl
    have hsplit : ∏ i : Fin D.R.rS, dd (Fin.castSucc i) =
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) *
          ∏ i : Fin D.R.rS, c v (Fin.castSucc i) := by
      rw [hdd, ← Finset.prod_mul_distrib]
    have hlastd : dd (Fin.last D.R.rS) = c v (Fin.last D.R.rS) := by
      rw [hdd]
      simp [dsc_last]
    have hG := (hc' v).2
    unfold Gv at hG
    rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_last, Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.dl_diag_r,
      Complex.sq_norm, Complex.sq_norm] at hG
    have hE : 0 < Complex.normSq
        (∏ i : Fin D.R.rS, star (dsc (D := D) lam sc (Fin.castSucc i)) * dsc (D := D) lam sc (Fin.castSucc i)) :=
      Complex.normSq_pos.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdsc _)
    unfold Formalism.QuantumDeterminants.Gf
    rw [hlast, hr, hTz u, hTz u', hsplit, hlastd]
    simp only [Complex.normSq_mul] at hG ⊢
    nlinarith [mul_pos hE hG]

end Formalism.L2.SG.RealObj.EnergyIntOm
