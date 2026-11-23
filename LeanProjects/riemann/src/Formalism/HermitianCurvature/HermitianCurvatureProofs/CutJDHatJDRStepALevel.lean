import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepABorder

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem base_index_ne_first_index (l : Fin r) (j : Fin (mdim k r l.succ)) : v0 k l j ≠ e0 k l := by
  unfold v0 e0
  intro h
  simp [Fin.ext_iff] at h

section Level
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ} {l : Fin r}
  {D : Set (Mx k r)}

variable (E l) in

def borderedMinorImage (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) {m : ℕ} (f b : Fin m → Fin (mdim k r l.succ)) (u : ℂ) :
    Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  bTee E l hD u * mB E l.succ (ho1 l hD) f b (u - 1) -
    ∑ w : Fin m, ∑ x : Fin m, ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledRowVectorOperator E l hD z (f w) * mB E l.succ (ho1 l hD) (f ∘ skip1 w) (b ∘ skip1 x) (u - 2) *
        (xv k r z' l.succ (b x) • 1))

variable (R : Rules) (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' l.castSucc D) {J : Mx k r → E}
  (hJ : SmoothLev k r l.castSucc D J) (hl : LeftEq k r z l.castSucc D J) (hr : RightEq k r z' l.castSucc D J)

include hz hz' hl hr in
theorem evaluation_bordered_minor_first {m : ℕ} (f b : Fin m → Fin (mdim k r l.succ)) (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (qminor (E0 E l.castSucc hD.1) (bE (e0 k l) (v0 k l ∘ f)) (bE (e0 k l) (v0 k l ∘ b)) u)
      (borderedMinorImage E l hD.1 z z' f b u) := by
  rw [quantum_minor_border_expansion_first _ (e0 k l) (v0 k l ∘ f) (v0 k l ∘ b) (level_generators_gl_relations R.gl l.castSucc hD.1) (fun _ => base_index_ne_first_index l _)
    (fun _ => base_index_ne_first_index l _) u]
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  refine IntJ.sub (((int_Tee R.w R.ep R.rt hD u).mul (int_minor R.w R.ep R.q hD f b (u - 1))).toJ hJ0)
    (IntJ.sum _ fun w _ => IntJ.sum _ fun x _ => IntJ.intMul ?_ _)
  exact ((int_we R.w R.ep R.rl hz hD (f w)).mul
    (int_minor R.w R.ep R.q hD (f ∘ skip1 w) (b ∘ skip1 x) (u - 2))).mulJ
    (intJ_eig hJ0 (eig_ex R.rr hz' hD.1 hJ hr (b x)))

include hz hz' hl hr in

theorem quantum_minor_point_evaluation {m : ℕ} (f b : Fin m → Fin (mdim k r l.succ)) (u : ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r}
    (hg : g ∈ Glev k r l.succ) (hgD : g ∈ Dc1 l D c) :
    qminorOp (EH k r) (posL k r l.castSucc ∘ bE (e0 k l) (v0 k l ∘ f)) (posL k r l.castSucc ∘ bE (e0 k l) (v0 k l ∘ b))
        u J (w1 k r l (c l) * g) =
      evP (ho1 l hD.1) (rho E R.w l hD.1 (J0 hD.1 hJ)) c g (borderedMinorImage E l hD.1 z z' f b u) := stp_evalPt R.w hD.1 hJ (evaluation_bordered_minor_first R hz hz' hD hJ hl hr f b u) hc hg hgD

end Level

section Comb

theorem sign_antisymmetric {m : ℕ} {a b : Fin m} (h : a ≠ b) : sg2 a b = -sg2 b a := by
  unfold sg2
  have hne : (a : ℕ) ≠ b := fun h' => h (Fin.ext h')
  split_ifs <;> first | omega | ring

private theorem skip1_val_eq_ite {n : ℕ} (a : Fin n) (b : Fin (n - 1)) :
    ((skip1 a b : Fin n) : ℕ) = if (b : ℕ) < a then (b : ℕ) else b + 1 := by
  unfold skip1
  split_ifs <;> rfl

private theorem skip2_val_eq_ite {n : ℕ} (a b : Fin n) (j : Fin (n - 2)) :
    ((skip2 a b j : Fin n) : ℕ) = if (j : ℕ) < a then (j : ℕ) else if (j : ℕ) + 1 < b then j + 1 else j + 2 := by
  unfold skip2
  split_ifs <;> rfl

private theorem skip1_eq_succAbove {t : ℕ} (s : Fin (t + 1)) (w : Fin t) : skip1 s w = s.succAbove w := by
  apply Fin.ext
  rw [skip1_val_eq_ite]
  by_cases h : (w : ℕ) < s
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt s w (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc s w (by rw [Fin.le_def, Fin.coe_castSucc]; omega)]
    simp

private theorem skip1_skip1_val_eq_skip2_min_max {t : ℕ} (s : Fin (t + 1)) (w : Fin t) (j : Fin (t + 1 - 2)) :
    ((skip1 s (skip1 w j) : Fin (t + 1)) : ℕ) = (skip2 (min (skip1 s w) s) (max (skip1 s w) s) j : ℕ) := by
  have hmin : ((min (skip1 s w) s : Fin (t + 1)) : ℕ) = min ((skip1 s w : Fin (t + 1)) : ℕ) (s : ℕ) := by
    rcases _root_.le_total (skip1 s w) s with h | h
    · rw [_root_.min_eq_left h, _root_.min_eq_left (Fin.le_def.mp h)]
    · rw [_root_.min_eq_right h, _root_.min_eq_right (Fin.le_def.mp h)]
  have hmax : ((max (skip1 s w) s : Fin (t + 1)) : ℕ) = max ((skip1 s w : Fin (t + 1)) : ℕ) (s : ℕ) := by
    rcases _root_.le_total (skip1 s w) s with h | h
    · rw [_root_.max_eq_right h, _root_.max_eq_right (Fin.le_def.mp h)]
    · rw [_root_.max_eq_left h, _root_.max_eq_left (Fin.le_def.mp h)]
  have hj := j.isLt
  have hw := w.isLt
  have hs := s.isLt
  rw [skip2_val_eq_ite, hmin, hmax, skip1_val_eq_ite s (skip1 w j), skip1_val_eq_ite s w, skip1_val_eq_ite w j]
  simp only [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

end Comb

section Alg
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {l : Fin r} {D : Set (Mx k r)}
  (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)

theorem aY_comm_bTee (t : Fin (mdim k r l.succ)) (u : ℂ) :
    mulB E l.succ (ho1 l hD) (aY z l.succ t) * bTee E l hD u = bTee E l hD u * mulB E l.succ (ho1 l hD) (aY z l.succ t) := by
  have h := P_mulB_of (E := E) (ho1 l hD) l (sf_aY z t) 0 (fun c _ g => by
    rw [zero_mul]; exact pOp_const l _ c)
  rw [zero_smul, add_zero] at h
  unfold bTee
  rw [mul_add, add_mul, h, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem capelli_key_first_term :
    (∑ s : Fin (mdim k r l.succ), ∑ t : Fin (mdim k r l.succ),
      ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k r z' l.succ s) •
        (mulB E l.succ (ho1 l hD) (aY z l.succ t) *
          (bTee E l hD (uC k r l.castSucc Y) * mB E l.succ (ho1 l hD) (skip1 s) (skip1 t) (uC k r l.castSucc Y - 1)))) =
      -(bTee E l hD (uC k r l.castSucc Y) * tB E l.succ (ho1 l hD) z z' Y 1 0) := by
  rw [stp_uC_succ, ← mul_neg, ← signed_expansion_block10, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← mul_assoc, aY_comm_bTee, mul_assoc, mul_smul_comm]

end Alg

section Comb2

theorem comb {M : Type*} [AddCommGroup M] [Module ℂ M] {t : ℕ} (β α' : Fin (t + 1) → ℂ)
    (Θ : Fin (t + 1) → Fin (t + 1) → (Fin (t + 1 - 2) → Fin (t + 1)) → (Fin (t + 1 - 2) → Fin (t + 1)) → M) :
    (∑ s : Fin (t + 1), ∑ T : Fin (t + 1), ∑ w : Fin t, ∑ x : Fin t,
      (((sg2 s (skip1 s w) * sg2 T (skip1 T x) : ℤ) : ℂ) * β s * α' (skip1 T x)) •
        Θ (skip1 s w) T (skip1 s ∘ skip1 w) (skip1 T ∘ skip1 x)) =
      -∑ w : Fin (t + 1), ∑ w' : Fin (t + 1), ∑ x : Fin (t + 1), ∑ x' : Fin (t + 1),
        if w ≠ w' ∧ x ≠ x' then (((sg2 w w' * sg2 x x' : ℤ) : ℂ) * (α' x' * β w')) •
          Θ w x (skip2 (min w w') (max w w')) (skip2 (min x x') (max x x')) else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 1; arg 2; ext w'; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [ite_and]
  rw [Fin.sum_univ_succAbove _ s]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_const_zero, zero_add, Fin.succAbove_ne,
    not_false_eq_true]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succAbove _ T]
  simp only [not_true_eq_false, ↓reduceIte, zero_add]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hTj : ¬T = T.succAbove j := (Fin.succAbove_ne T j).symm
  rw [if_pos hTj, ← skip1_eq_succAbove s i, ← skip1_eq_succAbove T j]
  have h1 : (skip1 s ∘ skip1 i : Fin (t + 1 - 2) → Fin (t + 1)) = skip2 (min (skip1 s i) s) (max (skip1 s i) s) :=
    funext fun k => Fin.ext (skip1_skip1_val_eq_skip2_min_max s i k)
  have h2 : (skip1 T ∘ skip1 j : Fin (t + 1 - 2) → Fin (t + 1)) = skip2 (min T (skip1 T j)) (max T (skip1 T j)) := by
    rw [_root_.min_comm, _root_.max_comm]
    exact funext fun k => Fin.ext (skip1_skip1_val_eq_skip2_min_max T j k)
  have hne : s ≠ skip1 s i := by
    rw [skip1_eq_succAbove s i]
    exact (Fin.succAbove_ne s i).symm
  rw [h1, h2, sign_antisymmetric hne, ← neg_smul]
  congr 1
  push_cast
  ring

theorem sign_skip_eq_power_at_level (L : Fin (r + 1)) (s : Fin (mdim k r L)) (w : Fin (mdim k r L - 1)) :
    sg2 s (skip1 s w) = (-1) ^ ((s : ℕ) + (w : ℕ)) := by
  unfold sg2 skip1
  by_cases hw : (w : ℕ) < s
  · simp [hw]
  · have h2 : ¬ ((w : ℕ) + 1 < s) := by omega
    simp only [hw, h2, ↓reduceIte, Fin.val_mk]
    ring

end Comb2

section Alg2
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {l : Fin r} {D : Set (Mx k r)}
  (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)

theorem capelli_key_second_term (s t : Fin (mdim k r l.succ)) (w x : Fin (mdim k r l.succ - 1)) (u : ℂ) :
    ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k r z' l.succ s) •
      (mulB E l.succ (ho1 l hD) (aY z l.succ t) *
        (((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
          (scaledRowVectorOperator E l hD z (skip1 s w) * mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) u *
            (xv k r z' l.succ (skip1 t x) • 1)))) =
      mulB E l.succ (ho1 l hD) (aCi k l) *
        ((((sg2 s (skip1 s w) * sg2 t (skip1 t x) : ℤ) : ℂ) * xbv k r z' l.succ s * xv k r z' l.succ (skip1 t x)) •
          (mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) *
            (mulB E l.succ (ho1 l hD) (aY z l.succ t) * mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) u))) := by
  unfold scaledRowVectorOperator
  rw [sign_skip_eq_power_at_level, sign_skip_eq_power_at_level]
  have c1 : mulB E l.succ (ho1 l hD) (aY z l.succ t) * mulB E l.succ (ho1 l hD) (aCi k l) = mulB E l.succ (ho1 l hD) (aCi k l) * mulB E l.succ (ho1 l hD) (aY z l.succ t) :=
    (mulB_comm (E := E) (ho1 l hD) (sf_aY z t) (sf_aCi l)).eq
  have c2 : mulB E l.succ (ho1 l hD) (aY z l.succ t) * mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) =
      mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) * mulB E l.succ (ho1 l hD) (aY z l.succ t) :=
    (mulB_comm (E := E) (ho1 l hD) (sf_aY z t) (sf_aYb z (skip1 s w))).eq
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_one, mul_assoc]
  rw [← mul_assoc (mulB E l.succ (ho1 l hD) (aY z l.succ t)) (mulB E l.succ (ho1 l hD) (aCi k l)), c1, mul_assoc,
    ← mul_assoc (mulB E l.succ (ho1 l hD) (aY z l.succ t)) (mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w))), c2, mul_assoc]
  congr 1
  push_cast
  ring

theorem capelli_key_second_identity :
    (∑ s : Fin (mdim k r l.succ), ∑ t : Fin (mdim k r l.succ),
      ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k r z' l.succ s) •
        (mulB E l.succ (ho1 l hD) (aY z l.succ t) *
          ∑ w : Fin (mdim k r l.succ - 1), ∑ x : Fin (mdim k r l.succ - 1),
            ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
              (scaledRowVectorOperator E l hD z (skip1 s w) *
                mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) (uC k r l.castSucc Y - 2) *
                (xv k r z' l.succ (skip1 t x) • 1)))) =
      mulB E l.succ (ho1 l hD) (aCi k l) * tB E l.succ (ho1 l hD) z z' Y 1 1 := by
  calc _ = mulB E l.succ (ho1 l hD) (aCi k l) * (∑ s : Fin (mdim k r l.succ), ∑ t : Fin (mdim k r l.succ), ∑ w : Fin (mdim k r l.succ - 1),
          ∑ x : Fin (mdim k r l.succ - 1),
          ((((sg2 s (skip1 s w) * sg2 t (skip1 t x) : ℤ) : ℂ) * xbv k r z' l.succ s *
            xv k r z' l.succ (skip1 t x)) •
            (mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) *
              (mulB E l.succ (ho1 l hD) (aY z l.succ t) * mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) (uC k r l.castSucc Y - 2))))) := by
        simp only [Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
        exact capelli_key_second_term hD z z' s t w x _
    _ = mulB E l.succ (ho1 l hD) (aCi k l) * -(∑ w : Fin (mdim k r l.succ), ∑ w' : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ),
          ∑ x' : Fin (mdim k r l.succ),
          if w ≠ w' ∧ x ≠ x' then (((sg2 w w' * sg2 x x' : ℤ) : ℂ) * (xv k r z' l.succ x' * xbv k r z' l.succ w')) •
            (mulB E l.succ (ho1 l hD) (aYb z l.succ w) * (mulB E l.succ (ho1 l hD) (aY z l.succ x) *
              mB E l.succ (ho1 l hD) (skip2 (min w w') (max w w')) (skip2 (min x x') (max x x')) (uC k r l.castSucc Y - 2))) else 0) := by
        exact congrArg (fun S => mulB E l.succ (ho1 l hD) (aCi k l) * S)
          (comb (fun s => xbv k r z' l.succ s) (fun x => xv k r z' l.succ x)
            (fun w x f b => mulB E l.succ (ho1 l hD) (aYb z l.succ w) * (mulB E l.succ (ho1 l hD) (aY z l.succ x) *
              mB E l.succ (ho1 l hD) f b (uC k r l.castSucc Y - 2))))
    _ = mulB E l.succ (ho1 l hD) (aCi k l) * tB E l.succ (ho1 l hD) z z' Y 1 1 := by
        rw [stp_uC_succ2, signed_double_expansion_block11, neg_neg]

end Alg2

end Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas
