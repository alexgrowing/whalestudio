import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocS

noncomputable section

open NumberField IsDedekindDomain Matrix Finset
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

def argC (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem quadratic_character_eq_additive (x : X.B.I.Gf) : X.chi2 x = X.psiEf (divN X.B.I X.B.g (argC X x)) := rfl

theorem argC_int {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : argC X x ∈ IntAf X.B.I.F X.B.I.E := by
  unfold argC
  refine add_mem (sum_mem fun a _ => ?_) (sum_mem fun i _ => ?_)
  · refine dual_hat_integral X.B.I _ (X.vectorsInLattice.1 a).2 _ (K_mv X.B.I hx ?_)
    unfold nxt; split_ifs
    · exact (X.vectorsInLattice.1 _).1
    · exact X.vectorsInLattice.2.1
  · split_ifs
    · exact dual_hat_integral X.B.I _ (X.vectorsInLattice.2.2 i).2 _ (K_mv X.B.I hx (X.vectorsInLattice.2.2 _).1)
    · exact zero_mem _

theorem sg_swap (x : X.B.I.Gf) (u v : VA X.B.I) :
    sg X.B.I (hhat X.B.I u (X.B.I.fmat x *ᵥ v)) = hhat X.B.I v (X.B.I.fmat x⁻¹ *ᵥ u) := by
  rw [hhat_conj]
  have := hhat_fmat X.B.I x v (X.B.I.fmat x⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
  exact this

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

def tW (ob : Bool) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : ZMod p :=
  (∑ a : Fin D.R.rS, if h : a.1 + 1 < D.R.rS then N (xI (hrD D) a) (xI (hrD D) ⟨a.1 + 1, h⟩)
      else N (xI (hrD D) a) (zI (hrD D))) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then (if ob then N (wI (hrD D) i) (wI (hrD D) ⟨i.1 + 1, h⟩) else 0) else 0

def tWc (ob : Bool) (N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : ZMod p :=
  (∑ a : Fin D.R.rS, if h : a.1 + 1 < D.R.rS then N' (yI (hrD D) (rv ⟨a.1 + 1, h⟩)) (yI (hrD D) (rv a))
      else -N' (zI (hrD D)) (yI (hrD D) (rv a))) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then
      (if ob then 0 else N' (wI (hrD D) (rv ⟨i.1 + 1, h⟩)) (wI (hrD D) (rv i))) else 0

theorem bw_Lq (hew : X.ew ∈ Wq X.B.I w) (i : Fin D.R.k) : X.bw i ∈ Lq X.B.I w := by
  rw [X.bw_w i]; exact Wq_smul hew (X.vectorsInLattice.2.2 i).1

theorem bwd_Lq (hsew : sg X.B.I X.ew ∈ Wq X.B.I w) (i : Fin D.R.k) : X.bwd i ∈ Lq X.B.I w := by
  rw [X.bwd_w i]; exact Wq_smul hsew (X.vectorsInLattice.2.2 i).2

theorem congC (ob : Bool) (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    CongW (w := w) p (argC X x) (tW (D := D) ob N) := by
  unfold argC tW
  refine congW_add (congW_sum _ fun a _ => ?_) (congW_sum _ fun i _ => ?_)
  · unfold nxt
    split_ifs with h
    · have := hN (xI (hrD D) a) (xI (hrD D) ⟨a.1 + 1, h⟩)
      rwa [dual_frame_isotropic, frame_isotropic] at this
    · have := hN (xI (hrD D) a) (zI (hrD D))
      rwa [dual_frame_isotropic, frame_anisotropic] at this
  · split_ifs with h hob
    · have := hN (wI (hrD D) i) (wI (hrD D) ⟨i.1 + 1, h⟩)
      rw [hob] at this
      rwa [frd_wt, fr_wt] at this
    · refine congW_zero_of (hhat_Lq_right (X.vectorsInLattice.2.2 i).2 (stab_w X.B.I w hx (bw_Lq X ?_ _)))
      simp only [hob, Bool.false_eq_true, if_false, sub_zero] at hew
      exact hew
    · exact congW_zero_of (zero_mem _)

theorem congW_of_sg {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {m : ZMod p} (h : CongW (w := w) p (sg X.B.I t) m) :
    CongW (w := wc X.B.I w) p t m := by
  have := (congW_sg (I := X.B.I) (w := w) (t := sg X.B.I t) (m := m)).2 h
  rwa [sg_sg] at this

theorem congCc (ob : Bool) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) {x : X.B.I.Gf}
    (hx : x ∈ X.B.I.Kset) {N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN' : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x⁻¹ *ᵥ fr X ob j)) (N' i j)) :
    CongW (w := wc X.B.I w) p (argC X x) (tWc (D := D) ob N') := by
  refine congW_of_sg X ?_
  unfold argC tWc
  rw [map_add, map_sum, map_sum]
  refine congW_add (congW_sum _ fun a _ => ?_) (congW_sum _ fun i _ => ?_)
  · unfold nxt
    split_ifs with h
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := hN' (yI (hrD D) (rv ⟨a.1 + 1, h⟩)) (yI (hrD D) (rv a))
      rwa [frd_y, fr_y, rv_rv, rv_rv] at this
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := congW_neg (hN' (zI (hrD D)) (yI (hrD D) (rv a)))
      rwa [dual_frame_anisotropic, fr_y, rv_rv, hhat_neg_left, neg_neg] at this
  · split_ifs with h hob
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      refine congW_zero_of (hhat_Lq_right (X.vectorsInLattice.2.2 _).1 (stab_w X.B.I w (K_inv X.B.I hx) (bwd_Lq X ?_ i)))
      simp only [hob, if_true, sub_zero] at hsew
      exact hsew
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := hN' (wI (hrD D) (rv ⟨i.1 + 1, h⟩)) (wI (hrD D) (rv i))
      simp only [hob, Bool.false_eq_true] at this ⊢
      rwa [frd_wf, fr_wf, rv_rv, rv_rv] at this
    · rw [map_zero]; exact congW_zero_of (zero_mem _)

theorem entN_eq {r : ℕ} (M : Matrix (Fin r) (Fin r) (ZMod p)) (i j : Fin r) {a b : ℕ} (ha : i.1 = a) (hb : j.1 = b) :
    M i j = entN M a b := by
  subst ha hb
  unfold entN
  rw [dif_pos ⟨i.2, j.2⟩]

theorem sum_eq (ob : Bool) {N N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hinv : ∀ i, i + 1 < D.R.r → entN N' i (i + 1) = -entN N i (i + 1)) :
    tW (D := D) ob N + tWc (D := D) ob N' = phiJ D.R.k D.R.rS (dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob) := by
  have hr := hrD D
  rw [phi_key hr ob hinv]
  unfold tW tWc
  have e1 : ∑ a : Fin D.R.rS, ((if h : a.1 + 1 < D.R.rS then N (xI hr a) (xI hr ⟨a.1 + 1, h⟩)
        else N (xI hr a) (zI hr)) + (if h : a.1 + 1 < D.R.rS then N' (yI hr (rv ⟨a.1 + 1, h⟩)) (yI hr (rv a))
        else -N' (zI hr) (yI hr (rv a)))) =
      ∑ a ∈ range D.R.rS, (if a + 1 < D.R.rS then entN N a (a + 1) +
        entN N' (D.R.rS + D.R.k + 1 + (D.R.rS - 2 - a)) (D.R.rS + D.R.k + 1 + (D.R.rS - 1 - a))
        else entN N a (D.R.rS + D.R.k) - entN N' (D.R.rS + D.R.k) (D.R.rS + D.R.k + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · have q1 : N (xI hr a) (xI hr ⟨a.1 + 1, h⟩) = entN N a.1 (a.1 + 1) := entN_eq N _ _ rfl rfl
      have q2 : N' (yI hr (rv ⟨a.1 + 1, h⟩)) (yI hr (rv a)) =
          entN N' (D.R.rS + D.R.k + 1 + (D.R.rS - 2 - a.1)) (D.R.rS + D.R.k + 1 + (D.R.rS - 1 - a.1)) :=
        entN_eq N' _ _ (by simp; omega) (by simp)
      rw [q1, q2]
    · have q1 : N (xI hr a) (zI hr) = entN N a.1 (D.R.rS + D.R.k) := entN_eq N _ _ rfl rfl
      have q2 : N' (zI hr) (yI hr (rv a)) = entN N' (D.R.rS + D.R.k) (D.R.rS + D.R.k + 1) :=
        entN_eq N' _ _ rfl (by simp; omega)
      rw [q1, q2]; ring
  have e2 : ∑ i : Fin D.R.k, ((if h : i.1 + 1 < D.R.k then (if ob then N (wI hr i) (wI hr ⟨i.1 + 1, h⟩) else 0) else 0) +
        (if h : i.1 + 1 < D.R.k then (if ob then 0 else N' (wI hr (rv ⟨i.1 + 1, h⟩)) (wI hr (rv i))) else 0)) =
      ∑ i ∈ range D.R.k, (if i + 1 < D.R.k then (if ob then entN N (D.R.rS + i) (D.R.rS + i + 1)
        else entN N' (D.R.rS + (D.R.k - 2 - i)) (D.R.rS + (D.R.k - 1 - i))) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h hob
    · have q1 : N (wI hr i) (wI hr ⟨i.1 + 1, h⟩) = entN N (D.R.rS + i.1) (D.R.rS + i.1 + 1) :=
        entN_eq N _ _ rfl (by simp; omega)
      rw [q1, add_zero]
    · have q1 : N' (wI hr (rv ⟨i.1 + 1, h⟩)) (wI hr (rv i)) =
          entN N' (D.R.rS + (D.R.k - 2 - i.1)) (D.R.rS + (D.R.k - 1 - i.1)) :=
        entN_eq N' _ _ (by simp; omega) (by simp)
      rw [q1, zero_add]
    · simp
  rw [← e1, ← e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end Formalism.L2.SG.Pf.KppLoc
