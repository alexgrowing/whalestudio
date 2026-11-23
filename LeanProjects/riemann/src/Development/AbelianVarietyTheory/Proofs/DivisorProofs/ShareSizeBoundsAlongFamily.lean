import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.ShareNumbers

theorem real_bounds (PP TO Dp k f m r nW : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hk : 1 ≤ k) (hD : 1 ≤ Dp) (hr : 1 ≤ r)
    (hPP : (2 * f * m) ^ 4 * nW ≤ PP) (hn40 : 40 ≤ nW) (hnk : k ≤ nW) (hnr : f * r ^ 2 ≤ nW)
    (hTO : PP ^ 4 * Dp ^ 3 * k * f / m ≤ TO) :
    54 * f * r ^ 4 ≤ TO ∧ 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ TO := by
  have hm0 : 0 < m := by linarith
  have hc : 16 ≤ (2 * f * m) ^ 4 := by
    have : 2 ≤ 2 * f * m := by nlinarith
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 4
  have hfm : f * m ≤ (2 * f * m) ^ 4 := by
    have h1 : 1 ≤ 2 * f * m := by nlinarith
    calc f * m ≤ 2 * f * m := by nlinarith
      _ = (2 * f * m) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ h1 (by norm_num)
  have hn0 : 0 ≤ nW := by linarith
  have hP640 : 640 ≤ PP := by nlinarith
  have hPm : m * nW ≤ PP := by nlinarith
  have hPfk : f * k ≤ PP := by nlinarith
  have hPfr : f * r ^ 2 ≤ PP := by nlinarith
  have hP0 : 0 ≤ PP := by linarith

  have h4 : PP ^ 3 ≤ PP ^ 4 / m := by
    rw [le_div_iff₀ hm0]
    have : m ≤ PP := by nlinarith
    calc PP ^ 3 * m ≤ PP ^ 3 * PP := by gcongr
      _ = PP ^ 4 := by ring
  have hDkf : 1 ≤ Dp ^ 3 * k * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hk) hf
  have hT : PP ^ 3 * (Dp ^ 3 * k * f) ≤ TO := by
    calc PP ^ 3 * (Dp ^ 3 * k * f) ≤ PP ^ 4 / m * (Dp ^ 3 * k * f) := by gcongr
      _ = PP ^ 4 * Dp ^ 3 * k * f / m := by ring
      _ ≤ TO := hTO
  have hP3 : 0 ≤ PP ^ 3 := by positivity
  constructor
  · have e1 : 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP ^ 3 := by
      have a : 54 * (f * r ^ 2) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * r ^ 2 := by positivity
      calc 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 54 * f * r ^ 4 ≤ 54 * (f * r ^ 2) * (f * r ^ 2) := by
      have : 0 ≤ r ^ 4 := by positivity
      have hff : f ≤ f * f := by nlinarith
      calc 54 * f * r ^ 4 = 54 * r ^ 4 * f := by ring
        _ ≤ 54 * r ^ 4 * (f * f) := by gcongr
        _ = _ := by ring
    calc 54 * f * r ^ 4 ≤ PP ^ 3 := e2.trans e1
      _ = PP ^ 3 * 1 := (mul_one _).symm
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT
  · have e1 : 28 * (f * k) * (f * k) ≤ PP ^ 3 := by
      have a : 28 * (f * k) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * k := by positivity
      calc 28 * (f * k) * (f * k) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by
      have hfk : 0 ≤ (f * k) ^ 3 := by positivity
      have hD2 : Dp * (Dp + 6) ≤ 7 * Dp ^ 3 := by
        have h1 : Dp ≤ Dp ^ 2 := by nlinarith
        have h2 : Dp ^ 2 ≤ Dp ^ 3 := by nlinarith
        nlinarith
      calc 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 4 * (f * k) ^ 3 * (7 * Dp ^ 3) := by gcongr
        _ = 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by ring
    calc _ ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := e2
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT

open Formalism.BasicNotions in

theorem params_bounds {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (p0 : ℕ) (hp : p0 ≤ D.R.r) :
    2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T.TO ∧
      (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / (T.TO : ℝ) ≤
        1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3)) := by
  have hf2 : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hDp : T.Dp = D.R.f * (D.R.r * (D.R.r - 1) / 2) := by rw [T.Dp_eq, Nat.choose_two_right]
  have hD1 : 1 ≤ T.Dp := by
    rw [T.Dp_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hnk : D.R.k ≤ T.nWn := by
    have h := T.nW_lo.2.1
    have h' : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnr : D.R.f * D.R.r ^ 2 ≤ T.nWn := by
    have h := T.nW_lo.1
    have h' : D.R.f * D.R.r * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ (by omega)
    calc D.R.f * D.R.r ^ 2 = D.R.f * D.R.r * D.R.r := by ring
      _ ≤ _ := h'.trans h
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast hm1
  have hTO : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
    have hn : 0 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f := by
      have : 0 ≤ T.PP ^ 4 := by positivity
      positivity
    have hd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    have hdm : (D.R.m : ℝ) * L.de2 ≤ D.R.m := mul_le_of_le_one_right hm0.le L.thickDensity_le_one
    calc T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m
        ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / ((D.R.m : ℝ) * L.de2) := div_le_div_of_nonneg_left hn hd hdm
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hn hx1) hd.le
  obtain ⟨A, B⟩ := real_bounds T.PP T.TO T.Dp D.R.k D.R.f D.R.m D.R.r T.nWn (by exact_mod_cast hm1)
    (by exact_mod_cast (show 1 ≤ D.R.f by omega)) (by exact_mod_cast hk1) (by exact_mod_cast hD1)
    (by exact_mod_cast (show 1 ≤ D.R.r by omega)) T.PP_nW (by exact_mod_cast T.nW_40) (by exact_mod_cast hnk)
    (by exact_mod_cast hnr) hTO
  constructor
  · have hA : 54 * (D.R.f * D.R.r ^ 4) ≤ T.TO := by
      have : ((54 * (D.R.f * D.R.r ^ 4) : ℕ) : ℝ) ≤ T.TO := by push_cast; linarith
      exact_mod_cast this
    have h1 : p0 * (D.R.r - p0) ≤ D.R.r * D.R.r := Nat.mul_le_mul hp (Nat.sub_le _ _)
    have h2 : 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * (D.R.f * D.R.r ^ 4) := by
      calc 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r)) := by gcongr
        _ = 50 * (D.R.f * D.R.r ^ 4) := by ring
    have h3 : D.R.r ≤ D.R.r ^ 4 := Nat.le_self_pow (by norm_num) _
    have h4 : 1 ≤ D.R.r ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h5 : D.R.r ^ 4 ≤ D.R.f * D.R.r ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [← hDp]
    have hT0 : (0 : ℝ) < T.TO := by
      have : 1 ≤ T.TO := le_trans (by omega) T.TO_40
      exact_mod_cast this
    have hq : (0 : ℝ) < 4 * ((D.R.f : ℝ) * D.R.k) ^ 3 := by
      have : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
      have : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
      positivity
    rw [div_le_div_iff₀ hT0 hq]
    linarith

end GlobalTheory.ShareNumbers

open GlobalTheory.ShareNumbers in

theorem GlobalTheory.ShareNumbers.numbers_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι p0 hp => params_bounds (Fm.parT x hx ι) p0 hp⟩⟩⟩
