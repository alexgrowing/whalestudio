import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.CNeZeroOfSame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem xv_apply (x v y : S.V) : xv S x v y = S.hT v y • x - S.hT x y • v := rfl

theorem xv_mem_LieN (F : FlagG S r T) (n : ℕ) (x v : S.V) (hx : x ∈ F.Xa (n + 1))
    (hv : ∀ y ∈ F.Xa (n + 1), S.hT v y = 0) : xv S x v ∈ F.LieN := by
  have hxX : x ∈ F.X := fXa_le_X F _ hx
  simp only [FlagG.LieN, LieU, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro w y
    have h1 := S.herm.eq v w
    have h2 := S.herm.eq x w
    simp only [xv_apply, map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply, h1, h2]
    ring
  · intro a _ _ w hw
    have hwX : w ∈ F.X := fXa_le_X F a hw
    rw [xv_apply, hT_X_X F hxX hwX, zero_smul, sub_zero]
    by_cases hna : n + 1 ≤ a - 1
    · exact Submodule.smul_mem _ _ (Xa_mono F hna hx)
    · rw [hv w (Xa_mono F (by omega) hw), zero_smul]
      exact zero_mem _
  · intro w hw
    have h0 : S.hT x w = 0 := hw x hxX
    rw [xv_apply, h0, zero_smul, sub_zero]
    exact Submodule.smul_mem _ _ hxX

theorem ell_xv (hS : CoefSmul) (hE : CoefE) (F : FlagG S r T) (i : Fin r) (v : S.V) :
    F.ell (xv S (F.e i) v) = S.hT v (F.fvec i.succ) := by
  unfold FlagG.ell
  have hterm : ∀ k : Fin r, F.coefX (xv S (F.e i) v (F.fvec k.succ)) k =
      if i = k then S.hT v (F.fvec k.succ) else 0 := by
    intro k
    rw [xv_apply, hT_X_fvec F (fe_mem_X F i), zero_smul, sub_zero,
      hS E S r T F _ _ k (fe_mem_X F i), hE E S r T F i k]
    split_ifs <;> simp
  simp only [hterm]
  rw [Finset.sum_ite_eq]
  simp

theorem ell'_xv (hA : CoefAdd) (hS : CoefSmul) (hE : CoefE) (hL : CoefLow)
    (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) (hs : SameFlag F F' c)
    (i : Fin r) (v : S.V) (hv : ∀ y ∈ F.Xa (i.val + 1), S.hT v y = 0) :
    F'.ell (xv S (F.e i) v) * c i.castSucc = c i.succ * S.hT v (F.fvec i.succ) := by
  have hXa := Xa_eq_of_same F F' c hs
  have hX := X_eq_of_same F F' c hs
  have heX' : F.e i ∈ F'.X := hX ▸ fe_mem_X F i
  have hir := i.2
  have hcoef : c i.castSucc * F'.coefX (F.e i) i = 1 := by
    have hsi := hs i.castSucc
    rw [fvec_castSucc, fvec_castSucc, Fin.val_castSucc] at hsi
    have hsi' : F'.e i + (-c i.castSucc) • F.e i ∈ F'.Xa i.val := by
      rw [neg_smul, ← sub_eq_add_neg, hXa i.val (by omega)]
      exact hsi
    have h0 := hL E S r T' F' i.val _ i hsi' le_rfl
    rw [hA E S r T' F' _ _ i (fe_mem_X F' i) (Submodule.smul_mem _ _ heX'),
      hS E S r T' F' _ _ i heX', hE E S r T' F' i i, if_pos rfl] at h0
    linear_combination -h0
  have hterm : ∀ k : Fin r, F'.coefX (xv S (F.e i) v (F'.fvec k.succ)) k =
      S.hT v (F'.fvec k.succ) * F'.coefX (F.e i) k := by
    intro k
    rw [xv_apply, hT_X_fvec F' heX', zero_smul, sub_zero, hS E S r T' F' _ _ k heX']
  have hzero : ∀ k : Fin r, k ≠ i → S.hT v (F'.fvec k.succ) * F'.coefX (F.e i) k = 0 := by
    intro k hk
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hk) with h | h
    · have hm : (k.succ).val < r := by rw [Fin.val_succ]; omega
      have hmem : F'.fvec k.succ ∈ F'.Xa (k.val + 1 + 1) := by
        have := fvec_mem_Xa F' k.succ hm
        rwa [Fin.val_succ] at this
      rw [hXa (k.val + 1 + 1) (by omega)] at hmem
      rw [hv _ (Xa_mono F (show k.val + 1 + 1 ≤ i.val + 1 by omega) hmem), zero_mul]
    · have hmem : F.e i ∈ F'.Xa (i.val + 1) := by
        rw [hXa (i.val + 1) (by omega)]
        exact e_mem_Xa F (by omega)
      rw [hL E S r T' F' (i.val + 1) _ k hmem (by omega), mul_zero]
  unfold FlagG.ell
  simp only [hterm]
  rw [Finset.sum_eq_single i (fun k _ hk => hzero k hk) (fun h => absurd (Finset.mem_univ i) h)]
  have hsucc : S.hT v (F'.fvec i.succ) = c i.succ * S.hT v (F.fvec i.succ) := by
    have h := hs i.succ
    rw [Fin.val_succ] at h
    have h2 := hv _ h
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
    exact h2
  rw [hsucc]
  linear_combination (c i.succ * S.hT v (F.fvec i.succ)) * hcoef

end PI.FRS
