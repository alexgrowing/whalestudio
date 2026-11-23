import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitCons

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem qbar_qbar (q : FreeE w) : qbar w (qbar w q) = q := by
  apply Subtype.ext
  simp only [qbar, pinv_pinv]

theorem hgt_qbar (q : FreeE w) : hgt w (qbar w q) = hgt w q := by
  unfold hgt qbar
  have h1 := pinv_add w q.1.1 q.1.2 q.2.2
  have h2 : q.1.1.val < q.1.2.val := q.2.1
  simp only
  omega

theorem sgm_pinv_eq (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm (pinv w c) (pinv w a) = (sgm a c : D.host.E) := by
  have h := sgm_pinv w a c hs
  rcases sgm_cases a c with e | e
  · rw [e, one_mul] at h; rw [h, e]
  · rw [e] at h ⊢; linear_combination -h

theorem sgq_qbar (q : FreeE w) : sgq w (qbar w q) = sgq w q :=
  sgm_pinv_eq w q.1.1 q.1.2 q.2.2

theorem Xinv_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y)⁻¹ q.1.1 q.1.2 = cf w y q - y q := by
  have h := inv_diff (Xmat_upU w y) (Xmat_upU w (trunc w y (hgt w q))) q.2.1 (fun i j hij hh => by
    by_cases hb : i < j ∧ blkOf w.1 i.val = blkOf w.1 j.val
    · simp only [Xmat, ne_of_lt hij, if_false, dif_pos hb, trunc]
      rw [if_pos (show hgt w ⟨(i, j), hb⟩ < hgt w q from hh)]
    · simp only [Xmat, ne_of_lt hij, if_false, dif_neg hb])
  rw [Xmat_q, Xmat_q] at h
  have h0 : trunc w y (hgt w q) q = 0 := by unfold trunc; rw [if_neg (lt_irrefl _)]
  rw [h0] at h
  unfold cf
  linear_combination h

theorem cf_mem (y : FreeE w → D.host.E) (q : FreeE w)
    (hy : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p)) : cf w y q ∈ ddPow D (hgt w q) := by
  unfold cf
  refine grD_inv (Xmat_upU w _) (Xmat_grD w _ fun p => ?_) q.1.1 q.1.2 (le_of_lt q.2.1)
  unfold trunc
  split_ifs with h
  · exact hy p h
  · exact FractionalIdeal.zero_mem _

theorem E_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 =
      y q - sgq w q * D.conjF (cf w y (qbar w q) - y (qbar w q)) := by
  rw [Matrix.sub_apply, Xmat_q]
  have h := Xinv_q w y (qbar w q)
  simp only [Psi]
  rw [show (Xmat w y)⁻¹ (pinv w q.1.2) (pinv w q.1.1) = cf w y (qbar w q) - y (qbar w q) from h]
  rfl

theorem condX_third (X : MatR D) (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) = (X - Psi w X⁻¹) (pinv w c) (pinv w a) := by
  rw [Matrix.sub_apply]
  simp only [Psi, pinv_pinv]
  rw [sgm_pinv_eq w a c hs]
  simp only [bt, sgm, map_mul, map_pow, map_neg, map_one]
  ring

theorem bt_mem {X : MatR D} (hG : GrD X) (a c : Fin (D.R.rS + 1)) (hac : a < c) :
    bt D X a c ∈ ddPow D (c.val - a.val) := by
  have h := hG a c (le_of_lt hac)
  rw [show bt D X a c = sgm a c * X a c by simp only [bt, sgm]; ring]
  rcases sgm_cases a c with e | e
  · rw [e, one_mul]; exact h
  · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h

theorem condX_iff (y : FreeE w → D.host.E) :
    CondX w (Xmat w y) ↔ (∀ q, y q ∈ ddPow D (hgt w q)) ∧
      ∀ q, (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
  constructor
  · intro h
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      intro q
      obtain ⟨h1, -, -⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
      have e := hgt_qbar w q
      unfold hgt at e
      simp only [qbar, pinv_pinv] at h1 e
      rw [e, Xmat_q] at h1
      exact h1
    refine ⟨hy, fun q => ?_⟩
    obtain ⟨-, -, h3⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
    rw [condX_third w _ _ _ (qbar w q).2.2] at h3
    have e := hgt_qbar w q
    unfold hgt at e
    simp only [qbar, pinv_pinv] at h3 e
    rw [e] at h3
    exact h3
  · rintro ⟨hy, hE⟩ a c hac hs
    have hG := grD_inv (Xmat_upU w y) (Xmat_grD w y hy)
    set p : FreeE w := qbar w ⟨(a, c), hac, hs⟩ with hp
    have hpe : hgt w p = c.val - a.val := hgt_qbar w _
    have hp1 : Xmat w y (pinv w c) (pinv w a) = y p := Xmat_q w y p
    refine ⟨?_, bt_mem hG a c hac, ?_⟩
    · rw [hp1, ← hpe]; exact hy p
    · rw [condX_third w _ a c hs, ← hpe]; exact hE p

end Formalism.L2.SG.Pf.StabIntLat
