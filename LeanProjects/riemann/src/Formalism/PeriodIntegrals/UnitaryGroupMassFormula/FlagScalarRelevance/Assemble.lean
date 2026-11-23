import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.XvMemLieN

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

theorem relevScalar_of (hD : DualExists) (hA : CoefAdd) (hS : CoefSmul) (hE : CoefE)
    (hL : CoefLow) (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] :
    RelevScalar E K := by
  intro S r T T' F F' c htr hT0 _ hs hrel
  have key : ∀ i : Fin r, c i.succ = c i.castSucc := by
    intro i
    have hir := i.2
    have hc := c_ne_zero_of_same F F' c hs i
    have hXa := Xa_eq_of_same F F' c hs
    have hrat : ∀ a : E,
        Algebra.trace K E a = Algebra.trace K E (c i.succ * a * (c i.castSucc)⁻¹) := by
      intro a
      obtain ⟨v, hv⟩ := hD E S (r + 1) F.fvec (fvec_indep F hT0) (Pi.single i.succ (star a))
      have hvf : ∀ k, S.hT v (F.fvec k) = star ((Pi.single i.succ (star a) : Fin (r + 1) → E) k) := by
        intro k
        rw [← S.herm.eq (F.fvec k) v, hv k, starRingEnd_apply]
      have hva : S.hT v (F.fvec i.succ) = a := by
        rw [hvf]
        simp
      have hv0 : ∀ y ∈ F.Xa (i.val + 1), S.hT v y = 0 := by
        refine hT_Xa_of F v _ (fun j hj => ?_)
        rw [← fvec_castSucc, hvf, Pi.single_apply, if_neg, star_zero]
        intro h
        have h' := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_succ] at h'
        omega
      have hF := xv_mem_LieN F i.val (F.e i) v (e_mem_Xa F (by omega)) hv0
      have hF' := xv_mem_LieN F' i.val (F.e i) v
        (by rw [hXa (i.val + 1) (by omega)]; exact e_mem_Xa F (by omega))
        (by rw [hXa (i.val + 1) (by omega)]; exact hv0)
      have h := hrel _ ⟨hF, hF'⟩
      unfold FlagG.dpsi at h
      rw [ell_xv hS hE F i v, hva] at h
      have h' := ell'_xv hA hS hE hL F F' c hs i v hv0
      rw [hva] at h'
      have h'' : F'.ell (xv S (F.e i) v) = c i.succ * a * (c i.castSucc)⁻¹ := by
        rw [← h', mul_assoc, mul_inv_cancel₀ hc, mul_one]
      rw [h, h'']
    have hzero : ∀ a : E, Algebra.trace K E ((c i.succ * (c i.castSucc)⁻¹ - 1) * a) = 0 := by
      intro a
      rw [sub_mul, one_mul, map_sub,
        show c i.succ * (c i.castSucc)⁻¹ * a = c i.succ * a * (c i.castSucc)⁻¹ by ring,
        ← hrat a, sub_self]
    have h1 := htr _ hzero
    rw [sub_eq_zero] at h1
    exact (mul_inv_eq_one₀ hc).1 h1
  intro i
  induction i using Fin.reverseInduction with
  | last => rfl
  | cast j ih => rw [← key j]; exact ih

end PI.FRS
