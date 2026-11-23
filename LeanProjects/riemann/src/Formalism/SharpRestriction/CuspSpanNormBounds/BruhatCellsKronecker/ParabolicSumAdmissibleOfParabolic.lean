import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.S.UnitaryVolumeMass MeasureTheory Formalism.QuantumDeterminants
open scoped ENNReal InnerProductSpace

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsNormSq_eq_sum (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

def hsVec (A : Wq →L[ℂ] Wp) : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))

theorem hsVec_norm_sq (A : Wq →L[ℂ] Wp) : ‖hsVec A‖ ^ 2 = hsNormSq A := by
  rw [hsNormSq_eq_sum, PiLp.norm_sq_eq_of_L2]
  rfl

theorem hsVec_sum_smul {ι : Type} [Fintype ι] (a : ι → ℂ) (X : ι → (Wq →L[ℂ] Wp)) :
    hsVec (∑ i, a i • X i) = ∑ i, a i • hsVec (X i) := by
  ext j
  simp [hsVec]

theorem hsNormSq_sum_le {ι : Type} [Fintype ι] (a : ι → ℂ) (X : ι → (Wq →L[ℂ] Wp)) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i, hsNormSq (X i) ≤ K) : hsNormSq (∑ i, a i • X i) ≤ K * (∑ i, ‖a i‖) ^ 2 := by
  have h1 : ‖hsVec (∑ i, a i • X i)‖ ≤ (∑ i, ‖a i‖) * Real.sqrt K := by
    rw [hsVec_sum_smul, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.le_sqrt_of_sq_le ?_
    rw [hsVec_norm_sq]; exact h i
  rw [← hsVec_norm_sq]
  calc ‖hsVec (∑ i, a i • X i)‖ ^ 2 ≤ ((∑ i, ‖a i‖) * Real.sqrt K) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = K * (∑ i, ‖a i‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]; ring

theorem hsNormSq_real_smul (c : ℝ) (A : Wq →L[ℂ] Wp) : hsNormSq (((c : ℝ) : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [_root_.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end HS

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

theorem jhUnit_le {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (νR : Measure (Mt D.R.k D.R.rS))
    (γ : MatKR D.R.k D.R.rS) (wt B : ℝ) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (wt * hsNormSq (A.J νR γ)) ≤ ENNReal.ofReal B * MMv D w w' A μsec) :
    wt * hsNormSq (jhUnit D w w' A μsec νR γ) ≤ B := by
  unfold jhUnit
  rw [hsNormSq_real_smul]
  by_cases hM : (MMv D w w' A μsec).toReal = 0
  · rw [hM, Real.zero_rpow (by norm_num)]
    simpa using hB
  · have hpos : 0 < (MMv D w w' A μsec).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
    have htop : MMv D w w' A μsec ≠ ⊤ := fun e => hM (by rw [e]; rfl)
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hB] at h
    have h2 : wt * hsNormSq (A.J νR γ) ≤ B * (MMv D w w' A μsec).toReal :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hpos.le)).1 h
    have h3 : ((MMv D w w' A μsec).toReal ^ (-(1 / 2 : ℝ))) ^ 2 = ((MMv D w w' A μsec).toReal)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
      norm_num
    rw [h3]
    calc wt * (((MMv D w w' A μsec).toReal)⁻¹ * hsNormSq (A.J νR γ))
        = (wt * hsNormSq (A.J νR γ)) * ((MMv D w w' A μsec).toReal)⁻¹ := by ring
      _ ≤ (B * (MMv D w w' A μsec).toReal) * ((MMv D w w' A μsec).toReal)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hpos.le)
      _ = B := by field_simp

theorem stPTsum_of_stPT (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ)
    (h : stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C) : stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro h0 τ w w' hTT θ hθ W hW ι _ lams As a hl μsec hsec γ p hrel θ' hθ' νR hν
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  set B : ℝ := large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
    (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2) with hBdef
  have hB : 0 ≤ B := by
    have : (0 : ℝ) < max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  set wt : ℝ := ptWeight D.R.k D.R.rS (Tr D w) (Tr D w') p with hwt
  have hi : ∀ i, wt * hsNormSq (jhUnit D w w' (As i) μsec νR γ) ≤ B := fun i =>
    jhUnit_le D w w' (As i) μsec νR γ wt B hB
      (h h0 τ w w' hTT θ hθ W hW (lams i) (hl i).1 (As i) (hl i).2 μsec hsec γ p hrel θ' hθ' νR hν)
  rcases le_or_gt wt 0 with hw | hw
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hw (hsNormSq_nonneg _)) (by positivity)
  · have hi' : ∀ i, hsNormSq (jhUnit D w w' (As i) μsec νR γ) ≤ B / wt := fun i => by
      rw [le_div_iff₀ hw, mul_comm]; exact hi i
    have := hsNormSq_sum_le a (fun i => jhUnit D w w' (As i) μsec νR γ) (B / wt) (by positivity) hi'
    calc wt * hsNormSq (∑ i, a i • jhUnit D w w' (As i) μsec νR γ)
        ≤ wt * (B / wt * (∑ i, ‖a i‖) ^ 2) := mul_le_mul_of_nonneg_left this hw.le
      _ = B * (∑ i, ‖a i‖) ^ 2 := by field_simp

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem ptsumF_of_ptF (Cg cb Cu cT CT C0 C1 : ℝ)
    (h : ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => stPT (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) :
    ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => stPTsum (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun Cn => (hC Cn).mono (fun C' Cl x i => stPTsum_of_stPT _ _ C' Cl Cg cb Cu cT CT C0 Cn C1 C)⟩

theorem PTsum_of_PT (Cg cb Cu cT CT C0 C1 : ℝ) (h : AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) :
    PX.PTsum Fm Cg cb Cu cT CT C0 C1 := ptsumF_of_ptF Fm Cg cb Cu cT CT C0 C1 h

theorem parabolic_sum_of_parabolic_family (Cg cb Cu cT CT C0 C1 : ℝ) (h : VanishingOnXAndXPlusBranching.admF1 Fm Cg cb Cu cT CT C0 C1) :
    PX.PTsum Fm Cg cb Cu cT CT C0 C1 := ptsumF_of_ptF Fm Cg cb Cu cT CT C0 C1 h

theorem PTsum_all (h : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) :
    ∀ Cg cb Cu cT CT C0 C1, PX.PTsum Fm Cg cb Cu cT CT C0 C1 :=
  fun Cg cb Cu cT CT C0 C1 => PTsum_of_PT Fm Cg cb Cu cT CT C0 C1 (h Cg cb Cu cT CT C0 C1)

theorem parabolic_sum_admissible_of_parabolic (Cg cb Cu cT CT C0 C1 : ℝ) (h : AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) :
    AuxiliaryNormPrimes.FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1 := ptsumF_of_ptF Fm Cg cb Cu cT CT C0 C1 h

end Fam

end Formalism.MainNotions.BridgeLemma

end
