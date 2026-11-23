import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

variable {D : D7} {L : SizeData₂ D}

theorem levelPrime_budget_of_fifth {C : ℝ} (h : ∀ u, product_first_zeroth_parts.WeightBudgetBound D u L C) : WeightDegreeSizes.LevelPrimeBudget D L C := by
  unfold WeightDegreeSizes.LevelPrimeBudget
  exact h

theorem setting_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u := by
  have key : ∀ X e : ℝ, 256 ≤ X → 0 < e → e < 1 / 52 →
      (4 : ℝ) ≤ X ^ (-(e / 100)) * Real.sqrt (X * X ^ (-(e / 8))) := by
    intro X e hX he he'
    have hX0 : 0 < X := by linarith
    have h1 : X * X ^ (-(e / 8)) = X ^ (1 + -(e / 8)) := by
      rw [Real.rpow_add hX0, Real.rpow_one]
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    have h256 : (4 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h256]
    calc (256 : ℝ) ^ ((1 : ℝ) / 4) ≤ X ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ (-(e / 100) + (1 + -(e / 8)) * (1 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  obtain ⟨Cn₀, hCn⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x2, hx2⟩ := hCn Cn₀ le_rfl 3 le_rfl
  obtain ⟨x3, hx3⟩ := hT
  refine ⟨max (max x2 x3) (max (Fm.x1 + 1) 256), fun x hx i u => ?_⟩
  have hxa : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : Fm.x1 < x := by
    have : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    linarith
  have h256 : (256 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hN, hW⟩ := hx2 x hxa i
  have hTu := (hx3 x hxb i).1
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have S := Fm.sizes x hx1 i
    have hM : SizeM (Fm.L x i) := S.2.1
    unfold SizeM szTh Scale.delta1 at hM
    have hX : (256 : ℝ) ≤ (Fm.L x i).sc.x := by
      rw [Fm.L_x x i hx1]
      exact h256
    have h4 := key _ _ hX (Fm.L x i).sc.eps_pos (Fm.L x i).sc.eps_lt
    exact_mod_cast h4.trans hM.1
  exact levelPrime_setting_of_sizes le_rfl hN hW hTu hm u

theorem family_levelPrime_budget {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (hB : product_first_zeroth_parts.BudF Fm) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x1, hx1⟩ := setting_fam Fm hT hDl
  obtain ⟨C, x0, hB⟩ := hB
  refine ⟨C, max x0 x1, fun x hx i => levelPrime_budget_of_fifth (fun u =>
    hB x (le_trans (le_max_left _ _) hx) i u (hx1 x (le_trans (le_max_right _ _) hx) i u))⟩

theorem gammaDiscriminant_budget_of_sizes {Cn cL CG : ℝ} (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hN : NumsL D L Cn cL) (hG : FactDGam D CG) :
    WeightDegreeSizes.StabiliserLogBound D L (4 * CG) := by
  unfold WeightDegreeSizes.StabiliserLogBound
  unfold FactDGam at hG
  intro u
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩ := hNu
  have hfk : D.R.f ≤ D.R.k := by
    unfold Ranks.f
    exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by
    unfold Ranks.f
    exact D.R.m_le_f
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hkN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    omega
  have hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hfk.trans hkN
  have hf2 : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hm2.trans hmf
  have hm2r : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  have hx1 := L.sc.one_lt_alt
  have hLr : 1 ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b := by
    field_simp
  rw [hbb] at hb'
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b := by
    have : (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      nlinarith
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L := by
    have hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L := by
      have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_right hN0.le hLr
      have hb : L.sc.b = Real.exp L.sc.L := rfl
      linarith
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log (Real.exp L.sc.L) := Real.log_le_log hN0 hNb
      _ = L.sc.L := Real.log_exp _
  have hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ) := Real.log_le_log (by linarith) hfN
  have hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L := by
    rw [Real.log_mul (by linarith) hN0.ne']
    linarith
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hb0' : 0 < L.sc.b := Real.exp_pos _
  have key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0 := by
    have h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤
        (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b :=
      mul_le_mul_of_nonneg_left hNL' (by positivity)
    have h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [hB0]
    nlinarith
  have hG' := hG u
  have := mul_le_mul_of_nonneg_left key hCG
  nlinarith

theorem family_gammaDiscriminant_budget {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (hG : DGamSize Fm) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨CG, x0, hG⟩ := hG
  obtain ⟨Cn₀, hCn⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x2, hx2⟩ := hCn Cn₀ le_rfl 3 le_rfl
  refine ⟨4 * max CG 0, max x0 x2, fun x hx i => ?_⟩
  exact gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hx2 x (le_trans (le_max_right _ _) hx) i).1
    (factDGam_mono (hG x (le_trans (le_max_left _ _) hx) i) (le_max_left _ _))

end Formalism.MainNotions.J

end
