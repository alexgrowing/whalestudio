import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdPowMulQd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Conj

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

include hA in
theorem dd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ ddPow D h) : D.conjF x ∈ ddPow D h := by
  rw [← locGlob _ (shapeNZ.1 h)] at hx ⊢
  exact fun p => locMem_conj δ M hA p hk (hx p)

include hA in
theorem qd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ qdPow D h) : D.conjF x ∈ qdPow D h := by
  rw [qdPow_mem_iff] at hx ⊢
  have := dd_conj δ M hA hk hx
  rwa [map_div₀, map_natCast] at this

end Conj

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : D.host.E) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩

variable (w : Point D.host.E (D.R.rS + 1))

def sgm (a c : Fin (D.R.rS + 1)) : D.host.E := (-1) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)

omit w in
theorem sgm_mul (a d c : Fin (D.R.rS + 1)) : sgm a d * sgm d c = sgm a c := by
  unfold sgm
  have := neg_one_pow_mul_self (D := D) (D.R.rS - d.val)
  linear_combination ((-1 : D.host.E) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)) * this

omit w in
theorem sgm_self (a : Fin (D.R.rS + 1)) : sgm a a = (1 : D.host.E) := neg_one_pow_mul_self _

omit w in
theorem sgm_conj (a c : Fin (D.R.rS + 1)) : D.conjF (sgm a c) = sgm a c := by
  simp [sgm, map_pow, map_neg, map_one]

omit w in
theorem sgm_cases (a c : Fin (D.R.rS + 1)) : sgm a c = (1 : D.host.E) ∨ sgm a c = -1 := by
  unfold sgm
  rw [← pow_add]
  exact neg_one_pow_eq_or _ _

theorem sgm_pinv (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm a c * sgm (pinv w c) (pinv w a) = (1 : D.host.E) := by
  unfold sgm
  have h1 := pinv_add w a c hs
  have ha := a.isLt; have hc := c.isLt; have ha' := (pinv w a).isLt; have hc' := (pinv w c).isLt
  rw [show ((-1 : D.host.E)) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val) *
      ((-1) ^ (D.R.rS - (pinv w c).val) * (-1) ^ (D.R.rS - (pinv w a).val)) =
      (-1) ^ ((D.R.rS - a.val) + (D.R.rS - c.val) + (D.R.rS - (pinv w c).val) + (D.R.rS - (pinv w a).val)) by ring]
  exact Even.neg_one_pow ⟨2 * D.R.rS - (pinv w a).val - a.val, by omega⟩

def Psi (Mt : MatR D) : MatR D := fun a c => sgm a c * D.conjF (Mt (pinv w c) (pinv w a))

def piPerm : Equiv.Perm (Fin (D.R.rS + 1)) := ⟨pinv w, pinv w, pinv_pinv w, pinv_pinv w⟩

theorem Psi_sub (A B : MatR D) : Psi w (A - B) = Psi w A - Psi w B := by
  funext a c; simp [Psi, map_sub, mul_sub]

theorem Psi_mul (A B : MatR D) : Psi w (A * B) = Psi w B * Psi w A := by
  funext a c
  simp only [Psi, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (piPerm w) _ _ (fun e => ?_)
  simp only [piPerm, Equiv.coe_fn_mk, pinv_pinv]
  rw [← sgm_mul a (pinv w e) c]; ring

theorem Psi_one : Psi w (1 : MatR D) = 1 := by
  funext a c
  simp only [Psi, Matrix.one_apply]
  by_cases h : a = c
  · subst h; simp [sgm_self]
  · have : pinv w c ≠ pinv w a := fun e => h (pinv_inj w e).symm
    simp [this, h]

theorem Psi_inv {A : MatR D} (hA : IsUnit A.det) : Psi w A⁻¹ = (Psi w A)⁻¹ := by
  have : Psi w A⁻¹ * Psi w A = 1 := by rw [← Psi_mul, Matrix.mul_nonsing_inv _ hA, Psi_one]
  exact (Matrix.inv_eq_left_inv this).symm

theorem Psi_Psi {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : Psi w (Psi w A) = A := by
  funext a c
  simp only [Psi, pinv_pinv, map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, sgm_conj]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · rw [← mul_assoc, sgm_pinv w a c hs, one_mul]
  · rw [hB a c hs, mul_zero, mul_zero]

theorem Psi_blk {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : IsBlockDiagonalMatrix w (Psi w A) := by
  intro a c hne
  have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
    rw [blkOf_pinv, blkOf_pinv]; exact fun e => hne e.symm
  simp only [Psi, hB _ _ this, map_zero, mul_zero]

theorem Psi_upU {A : MatR D} (hU : UpU A) (hB : IsBlockDiagonalMatrix w A) : UpU (Psi w A) := by
  intro a c
  refine ⟨fun hca => ?_, fun hac => ?_⟩
  · simp only [Psi]
    by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
    · have := (pinv_lt_iff w c a hs.symm).1 hca
      rw [(hU _ _).1 this, map_zero, mul_zero]
    · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      rw [hB _ _ this, map_zero, mul_zero]
  · subst hac; simp [Psi, sgm_self, (hU _ _).2 rfl]

theorem Psi_grD (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {A : MatR D} (hB : IsBlockDiagonalMatrix w A) (hG : GrD A) : GrD (Psi w A) := by
  intro a c hac
  simp only [Psi]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · have hle : pinv w c ≤ pinv w a := by
      rcases eq_or_lt_of_le hac with h | h
      · rw [h]
      · exact le_of_lt ((pinv_lt_iff w a c hs).1 h)
    have hh : (pinv w a).val - (pinv w c).val = c.val - a.val := by
      have := pinv_add w a c hs; omega
    have h1 := hG _ _ hle
    rw [hh] at h1
    have h2 := dd_conj δ M hA (by have := c.isLt; omega) h1
    rcases sgm_cases a c with e | e
    · rw [e, one_mul]; exact h2
    · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h2
  · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
      rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
    rw [hB _ _ this, map_zero, mul_zero]; exact FractionalIdeal.zero_mem _

theorem blk_inv {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : IsBlockDiagonalMatrix w X⁻¹ := by
  obtain ⟨hlo, hXi, hW, -⟩ := st_of_X w hU hB
  set β := ptMat w * X * (ptMat w)⁻¹
  have hu := ptMat_isUnit w
  have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hlo)]; exact isUnit_one
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hW' : β⁻¹ * ptMat w * X = ptMat w := by
    have : ptMat w * X⁻¹ = β⁻¹ * ptMat w := by
      calc ptMat w * X⁻¹ = β⁻¹ * (β * ptMat w * X⁻¹) := by
            rw [Matrix.mul_assoc β]; exact (Matrix.nonsing_inv_mul_cancel_left β _ hβd).symm
        _ = β⁻¹ * ptMat w := by rw [hW]
    rw [← this, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hXd, Matrix.mul_one]
  obtain ⟨h1, -, h3⟩ := X_of_st w (loU_inv (show LoU β from hlo)) hU hW'
  rw [h1] at h3
  exact h3

end Formalism.L2.SG.Pf.StabIntLat
