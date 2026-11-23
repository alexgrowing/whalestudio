import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDivSqrtLeFourExp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem tieAdmG_of_record (D : Formalism.BasicNotions.D7) : TieAdmG D :=
  fun k => ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

theorem wg_le_badBound (g m N q : ℝ) (n : ℕ) (r : ℝ) (hg : 2 ≤ g) (hm : 0 ≤ m) (hr : 100 ≤ r) (hrN : r ≤ N) :
    3 * (n : ℝ) / g + 23 * (n : ℝ) * Real.log g / Real.sqrt g +
        2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) + r / 2 * (7 / 8 : ℝ) ^ n +
        Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ badBound g n m N q := by
  unfold badBound
  have hf : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos (by linarith)
  have hlN : Real.log r ≤ Real.log N := Real.log_le_log hr0 hrN
  have hg1 : 0 < g - 1 := by linarith
  have t3 : 2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) ≤
      2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) := by
    have : (1 + Real.log r) / (g - 1) ≤ (1 + Real.log N) / (g - 1) :=
      div_le_div_of_nonneg_right (by linarith) hg1.le
    have h0 : 0 ≤ 2 * (n : ℝ) * m := by positivity
    nlinarith
  have t4 : r / 2 * (7 / 8 : ℝ) ^ n ≤ N / 2 * (7 / 8 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    have : 0 ≤ (7 / 8 : ℝ) ^ n := by positivity
    nlinarith
  have t5 : Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ Real.exp (-((n : ℝ) / (10 * Real.log N))) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hf (by positivity) (by linarith)
  linarith

end GlobalTheory.BadNumOnto

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem badShare_numbers_onto : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  refine ⟨1, one_pos, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨xs, hs⟩ := GlobalTheory.family_eventually_size_bounds eps Fm 5 (by norm_num)
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hezle : Fm.ez ≤ eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.ez_le
    rwa [Fm.L_ez 0 i, Fm.L_eps 0 i] at this
  obtain ⟨xb, hb⟩ := badBound_numbers Fm.ez 5 hez (hezle.trans he1)
  have he7 : 0 < Fm.ez / 7 := by positivity
  obtain ⟨xe, hxe⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop he7).eventually_ge_atTop (4 : ℝ)).and
      (((tendsto_rpow_atTop he).eventually_ge_atTop (512 : ℝ)).and (Filter.eventually_ge_atTop (1 : ℝ))))
  refine ⟨max (max xs xb) xe, fun x hx1 hx ι => ?_⟩
  have hxs : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxb : xb ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  obtain ⟨h7, h512, hx1'⟩ := hxe x ((le_max_right _ _).trans hx)
  rw [Fm.L_x x ι hx1, Fm.L_ez x ι]
  have hE : Real.exp (-(x ^ (Fm.ez / 7))) ≤ 1 / 4 := by
    have h1 : (4 : ℝ) ≤ Real.exp (x ^ (Fm.ez / 7)) := by
      have := Real.add_one_le_exp (x ^ (Fm.ez / 7)); linarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h1
  have hr100 : 100 ≤ (Fm.D x ι).R.r := (hs x hxs ι 0).2.2.2.2.1
  refine ⟨hr100, tieAdmG_of_record _, hE, fun k => ?_⟩
  obtain ⟨hg, hf2, hf5, hm5, -, hr5, hq⟩ := hs x hxs ι k
  have hg12 : (2 : ℝ) ^ 12 ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans ?_ hg
    have := Real.add_one_le_exp (8 * x ^ eps)
    norm_num
    linarith
  refine ⟨by exact_mod_cast hg12, ?_⟩
  have hr100' : (100 : ℝ) ≤ ((Fm.D x ι).R.r : ℝ) := by exact_mod_cast hr100
  have hepsC : x ^ Fm.ez ≤ x ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hgz : Real.exp (8 * x ^ Fm.ez) ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans (Real.exp_le_exp.2 ?_) hg
    have := Real.rpow_le_rpow_of_exponent_le hx1' hezle
    linarith
  obtain ⟨-, hbb0, hbb⟩ := hb x hxb ((Fm.D x ι).host.g k) ((Fm.D x ι).R.f) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) hgz
    (by rw [Real.rpow_two]; exact hf2) hf5 (Nat.cast_nonneg _) hm5 (le_max_right _ _) (max_le hr5 hepsC) hq
  have hW := wg_le_badBound ((Fm.D x ι).host.g k) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) ((Fm.D x ι).R.f)
    ((Fm.D x ι).R.r) (by linarith) (Nat.cast_nonneg _) hr100' (le_max_left _ _)
  linarith

end GlobalTheory.BadNumOnto
