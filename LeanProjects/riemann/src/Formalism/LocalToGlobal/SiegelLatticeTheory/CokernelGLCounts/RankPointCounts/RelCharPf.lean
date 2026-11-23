import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMain
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApproxFinal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinBound

noncomputable section

open scoped Classical ComplexConjugate
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.Level Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Pf.RelChar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section abelian₂

variable {D : D7} (X : HidaSetting D)

def lamU (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (A : Matrix (Kap X) (Kap X) ℂ) : ℂ :=
  ∑ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a))
    ((Bv X v * A * Bv' X v) *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a)

theorem lamU_add (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (A B : Matrix (Kap X) (Kap X) ℂ) :
    lamU X w v (A + B) = lamU X w v A + lamU X w v B := by
  unfold lamU
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, hJ, Matrix.mulVec_add, dotProduct_add]

theorem lamU_smul (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (c : ℂ) (A : Matrix (Kap X) (Kap X) ℂ) :
    lamU X w v (c • A) = c * lamU X w v A := by
  unfold lamU
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ∀ (B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (y : Fin X.B.I.n → ℂ), (c • B) *ᵥ y = c • (B *ᵥ y) := by
    intro B y; ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e, hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

def lamL (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Matrix (Kap X) (Kap X) ℂ →ₗ[ℂ] ℂ where
  toFun := lamU X w v
  map_add' := lamU_add X w v
  map_smul' c A := by rw [lamU_smul]; rfl

theorem hfe_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
  rw [hJ_rv, Vanish2.hE_f_e]
  split_ifs <;> simp

theorem hfz_v (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR w)) = 0 := by
  rw [hJ_rv, Vanish2.hermitian_f_z_zero, map_zero]

theorem lamU_one (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) : lamU X w v 1 = 0 := by
  unfold lamU
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.mul_one, Bv_mul_Bv', Matrix.one_mulVec]
  unfold nxt
  split_ifs with h
  · rw [hfe_v, if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp at this
  · exact hfz_v X w v a

theorem rc_sum_eq (w : D.what₂.Word) (s : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ∑ a, rootCoord (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (fun b => rv X.B.I v (X.fR b))
      (rv X.B.I v (X.zR w)) (uMat (s v)) a = lamU X w v (Mv X v s) := by
  unfold lamU rootCoord
  rw [uMat_eq X v s]

end abelian₂

def LamPat2 : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (w : D.what₂.Word) (v : InfinitePlace X.B.I.F) (A : Matrix (Kap X) (Kap X) ℂ),
    InPat (lvk X) 2 A → lamU X w v A = 0

def RatVanish : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Yf : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Yf.what₂ u) (Yf.what₂ u')), t.relevant →
    ∀ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    (∀ y, X.crd (t.lin y) = (M : Matrix _ _ _) *ᵥ X.crd y) →
    ∀ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Y →
      InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _)) → Yᴴ * JB X = -(JB X * Y) →
      ∀ v, (lamU X u v (Y.map (X.B.I.φ v)) -
        lamU X u' v ((Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _)).map (X.B.I.φ v))).re = 0

section Main

theorem lin_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ i j, ‖B i j‖ ≤ C) → ‖L B‖ ≤ K * C := by
  first | exact UpperTheory.Reformulated.B.Qj19.lin_bound .. | (apply UpperTheory.Reformulated.B.Qj19.lin_bound <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj19.lin_bound <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj19.lin_bound <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj19.lin_bound <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj19.lin_bound <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj19.lin_bound ι ‹_› ‹_› L | exact @UpperTheory.Reformulated.B.Qj19.lin_bound ι ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qj19.lin_bound ι ‹_› | exact @UpperTheory.Reformulated.B.Qj19.lin_bound ι

theorem eq_zero_of_nat_mul_le {x K : ℝ} (h : ∀ m : ℕ, 1 ≤ m → |(m : ℝ) * x| ≤ K) : x = 0 := by
  by_contra hx
  have hpos : 0 < |x| := abs_pos.2 hx
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (K / |x|))
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast this.le
  have h1 := h m hm1
  rw [abs_mul, Nat.abs_cast] at h1
  have h2 : K / |x| < m := lt_of_le_of_lt (le_max_right _ _) hm
  have h3 : K < m * |x| := by rwa [div_lt_iff₀ hpos] at h2
  linarith

theorem re_add_star (z : ℂ) : z + star z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp; ring

theorem relCharC_of (h3 : LamPat2) (h4 : RatVanish) : RelCharC := by
  intro D X Yf u u' t ht r hr
  obtain ⟨M, hMU, hMx, -, hMc⟩ := t.rep.2.1
  have hx : ∀ v, uMat (t.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix _ _ _).map (X.B.I.φ v) * X.B.I.P v := hMx
  let G : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ := fun v => (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)
  let G' : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ :=
    fun v => (Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v)
  have hGG : ∀ v, G v * G' v = 1 :=
    fun v => by simp only [G, G']; rw [← Matrix.map_mul, rcm_gr_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGu : ∀ v, (G v)ᴴ * JBv X v * G v = JBv X v := fun v => by
    simp only [G]; rw [← rcm_mv_rat X hx v]; exact Mv_unitary X v _
  have hx1 := (rcm_rset_iff t hx r).1 hr
  let Λ : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ →ₗ[ℂ] ℂ := fun v =>
    lamL X u v - (lamL X u' v).comp ((LinearMap.mulRight ℂ (G v)).comp (LinearMap.mulLeft ℂ (G' v)))
  have hΛ : ∀ v B, Λ v B = lamU X u v B - lamU X u' v (G' v * B * G v) := fun v B => rfl
  let P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ := fun v => proj (JBv X v) (JBv' X v) (Mv X v r - 1)
  have hPk : ∀ v, InPat (lvk X) 1 (P v) := fun v => inPat_proj (JBv_graded X v) (JBv'_graded X v) (hx1 v).1
  have hPs : ∀ v, (P v)ᴴ * JBv X v = -(JBv X v * P v) :=
    fun v => proj_skew (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v) (JBv_mul X v) _
  have e2 : ∀ v, G' v * (Mv X v r - 1) * G v = G' v * Mv X v r * G v - 1 := fun v => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_comm_one (hGG v)]
  have hcp : ∀ v, G' v * P v * G v = proj (JBv X v) (JBv' X v) (G' v * Mv X v r * G v - 1) := fun v => by
    show G' v * proj (JBv X v) (JBv' X v) (Mv X v r - 1) * G v = _
    rw [conj_proj (JBv_herm X v) (JBv'_herm X v) (JBv'_mul X v) (JBv_mul X v) (hGu v) (hGG v), e2]
  have hx2 : ∀ v, InPat (lvk X) 1 (G' v * Mv X v r * G v - 1) := fun v => (hx1 v).2
  have hPc : ∀ v, InPat (lvk X) 1 (G' v * P v * G v) := fun v => by
    rw [hcp]; exact inPat_proj (JBv_graded X v) (JBv'_graded X v) (hx2 v)

  have hstep : ∀ v, lamU X u v (Mv X v r) - lamU X u' v (Mv X v (t.pt.1⁻¹ * r * t.pt.1)) = Λ v (P v) := by
    intro v
    rw [rcm_mv_conj hx, hΛ]
    have hA2 : InPat (lvk X) (1 + 1) ((Mv X v r - 1) - P v) :=
      sub_proj_of_unitary (JBv_graded X v) (JBv'_graded X v) (JBv'_mul X v) (Mv_unitary X v r) (hx1 v).1
    have hu' : (G' v * Mv X v r * G v)ᴴ * JBv X v * (G' v * Mv X v r * G v) = JBv X v := by
      simp only [G, G']; rw [← rcm_mv_conj hx]; exact Mv_unitary X v _
    have hB2 : InPat (lvk X) (1 + 1) ((G' v * Mv X v r * G v - 1) - G' v * P v * G v) := by
      rw [hcp]
      exact sub_proj_of_unitary (JBv_graded X v) (JBv'_graded X v) (JBv'_mul X v) hu' (hx2 v)
    have l1 : lamU X u v (Mv X v r) = lamU X u v (P v) := by
      have e : Mv X v r = ((Mv X v r - 1) - P v) + P v + 1 := by abel
      rw [e, lamU_add, lamU_add, lamU_one, h3 D X u v _ hA2, zero_add, add_zero]
    have l2 : lamU X u' v (G' v * Mv X v r * G v) = lamU X u' v (G' v * P v * G v) := by
      have e : G' v * Mv X v r * G v = ((G' v * Mv X v r * G v - 1) - G' v * P v * G v) + G' v * P v * G v + 1 := by
        abel
      rw [e, lamU_add, lamU_add, lamU_one, h3 D X u' v _ hB2, zero_add, add_zero]
    rw [l1, l2]

  obtain ⟨C, hC⟩ := ratApprox_holds D X M hMU 1 le_rfl 1 le_rfl
  have hvan : ∀ v, (Λ v (P v)).re = 0 := by
    intro v
    obtain ⟨K, hK0, hK⟩ := lin_bound (Λ v)
    refine eq_zero_of_nat_mul_le (K := K * C) fun m hm => ?_
    have hmP : ∀ w, ((m : ℂ) • P w)ᴴ * JBv X w = -(JBv X w * ((m : ℂ) • P w)) := by
      intro w
      rw [conjTranspose_smul, Matrix.smul_mul, hPs, Matrix.mul_smul, smul_neg]
      congr 2
      simp
    obtain ⟨Y, hY1, hYc, hYs, -, hYC⟩ := hC (fun w => (m : ℂ) • P w) fun w =>
      ⟨inPat_smul _ (hPk w), by rw [Matrix.mul_smul, Matrix.smul_mul]; exact inPat_smul _ (hPc w), hmP w⟩
    have hR := h4 D X Yf u u' t ht M hMU hMc Y hY1 hYc hYs v
    have hΛY : (Λ v (Y.map (X.B.I.φ v))).re = 0 := by
      rw [hΛ]
      have : G' v * Y.map (X.B.I.φ v) * G v =
          (Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _)).map (X.B.I.φ v) := by
        simp only [G, G', Matrix.map_mul]
      rw [this]
      exact hR
    have hbd : ‖Λ v ((m : ℂ) • P v - Y.map (X.B.I.φ v))‖ ≤ K * C := by
      refine hK _ C fun i j => ?_
      have := hYC v i j
      rw [Matrix.sub_apply] at this ⊢
      rwa [norm_sub_rev]
    have hre : (Λ v ((m : ℂ) • P v)).re = (m : ℝ) * (Λ v (P v)).re := by
      rw [map_smul, smul_eq_mul, Complex.mul_re]
      simp
    calc |(m : ℝ) * (Λ v (P v)).re| = |(Λ v ((m : ℂ) • P v - Y.map (X.B.I.φ v))).re| := by
          rw [map_sub, Complex.sub_re, hΛY, sub_zero, hre]
      _ ≤ ‖Λ v ((m : ℂ) • P v - Y.map (X.B.I.φ v))‖ := Complex.abs_re_le_norm _
      _ ≤ K * C := hbd

  unfold HidaSetting.psiInfU psiInf
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold psiR
  have hsum : ∀ (w : D.what₂.Word) (s : X.B.I.Ginf),
      (∑ a, (rootCoord (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (fun b => rv X.B.I v (X.fR b))
        (rv X.B.I v (X.zR w)) (uMat (s v)) a + star (rootCoord (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b))
        (fun b => rv X.B.I v (X.fR b)) (rv X.B.I v (X.zR w)) (uMat (s v)) a))) =
      ((2 * (lamU X w v (Mv X v s)).re : ℝ) : ℂ) := by
    intro w s
    rw [Finset.sum_add_distrib, ← star_sum, rc_sum_eq, re_add_star]
  rw [hsum u r, hsum u' (t.pt.1⁻¹ * r * t.pt.1)]
  have hd := congrArg Complex.re (hstep v)
  rw [Complex.sub_re, hvan v, sub_eq_zero] at hd
  rw [hd]

theorem lamPat2_holds : LamPat2 := by
  intro D X w v A hA
  unfold lamU
  refine Finset.sum_eq_zero fun a _ => ?_
  have hc : ∀ j, (Bv' X v *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a) j ≠ 0 →
      lvk X j ≤ a.1 + 2 := by
    intro j hj
    by_cases h : a.1 + 1 < D.R.rS
    · have hy : nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a =
          rv X.B.I v (bv X (Sum.inl ⟨a.1 + 1, h⟩)) := by
        unfold nxt; rw [dif_pos h]; rfl
      rw [hy, Bv'_rv, Pi.single_apply] at hj
      split_ifs at hj with hjj
      · subst hjj; simp [lvk]
      · exact absurd rfl hj
    · have hy : nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a = rv X.B.I v (X.zR w) := by
        unfold nxt; rw [dif_neg h]
      rcases j with b | i | b
      · simp only [lvk, Sum.elim_inl]; omega
      · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; omega
      · exfalso; apply hj
        have h1 := hJ_e_Bv X v b (Bv' X v *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a)
        rw [Matrix.mulVec_mulVec, Bv_mul_Bv', Matrix.one_mulVec, hy, hermitian_basis_e_z_orthogonal X w v b] at h1
        rw [hy]; exact h1.symm
  have hAc : Bv X v *ᵥ (A *ᵥ (Bv' X v *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a)) ∈
      Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' {b : Fin D.R.rS | b.1 < a.1}) := by
    refine Bv_mulVec_mem X v _ _ fun k hk => ?_
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hcj : (Bv' X v *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a) j = 0
    · rw [hcj, mul_zero]
    · have hl := hc j hcj
      rw [hA k j ?_, zero_mul]
      rcases k with b | i | b
      · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
        simp only [lvk, Sum.elim_inl] at hl ⊢; omega
      · simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hl ⊢; have := a.2; omega
      · simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hl ⊢; have := a.2; have := b.2; omega
  have e : (Bv X v * A * Bv' X v) *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a =
      Bv X v *ᵥ (A *ᵥ (Bv' X v *ᵥ nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR w)) a)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  exact Vanish2.hJ_spL (X.B.I.ε v) _ _ (fun a b => hfe_v X v a b) a hAc

theorem relCharC_of_rat (h4 : RatVanish) : RelCharC := relCharC_of lamPat2_holds h4

end Main

end Formalism.L2.SG.Pf.RelChar
