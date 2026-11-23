import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SizeQ

theorem one_le_size (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  refine Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun τ _ => ?_)
  exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun l _ => le_max_left _ _)

private lemma one_add_logb_two_mul_le_of_log_le_sqrt (f r : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hlog : Real.log f ≤ Real.sqrt r) : 1 + Real.logb 2 (2 * (f : ℝ)) ≤ 2 * (r : ℝ) + 2 := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hsq : Real.sqrt r ≤ r := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsplit : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.log f / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hf0.ne', add_div, div_self (by linarith)]
  have hdiv : Real.log f / Real.log 2 ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem classNumber_le (D : D7) (b : ℝ) (hb : 1 ≤ b) (hrd : D.host.rdE ≤ b) (hf : 1 ≤ D.R.f)
    (hr : 1 ≤ D.R.rS) (hlog : Real.log D.R.f ≤ Real.sqrt D.R.rS) :
    (classNumber D.host.E : ℝ) ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
  obtain ⟨-, hdeg, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D
  have hcn := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.classNumberBound D.host.E
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hdeg' : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by rw [hdeg]; push_cast; ring

  have hdisc : |(NumberField.discr D.host.E : ℝ)| = D.host.rdE ^ (2 * (D.R.f : ℝ)) := by
    rw [Formalism.BasicNotions.Host.rdE, hdeg', ← Real.rpow_mul (abs_nonneg _), one_div,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  rw [hdisc, hdeg', ← Real.rpow_mul (by linarith)] at hcn
  have hc := one_add_logb_two_mul_le_of_log_le_sqrt D.R.f D.R.rS hf hr hlog
  have hf1r : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hlb : 0 ≤ Real.logb 2 (2 * (D.R.f : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  calc (classNumber D.host.E : ℝ)
      ≤ D.host.rdE ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) := hcn
    _ ≤ b ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) :=
        Real.rpow_le_rpow (by linarith) hrd (by positivity)
    _ ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        rw [hm']
        nlinarith

private lemma le_rpow_abs_div_eight_of_mul_pow_le (k b Cg g : ℝ) (hk : 0 ≤ k) (hb : 1 ≤ b) (h1 : (k * b) ^ 8 ≤ g)
    (h2 : g ≤ b ^ Cg) : k ≤ b ^ (|Cg| / 8) := by
  have hk8 : k ^ 8 ≤ b ^ |Cg| := by
    calc k ^ 8 ≤ (k * b) ^ 8 := by
          apply pow_le_pow_left₀ hk; nlinarith
      _ ≤ b ^ Cg := h1.trans h2
      _ ≤ b ^ |Cg| := Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _)
  by_contra hlt
  push_neg at hlt
  have hpos : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg (by linarith) _
  have := pow_lt_pow_left₀ hlt hpos (by norm_num : (8 : ℕ) ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at this
  norm_num at this
  linarith

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  intro Cg cb Cu cT CT C0 A
  refine ⟨|Cg| / 8 + 3 / 2 + 6, ?_⟩
  intro C hC D large₂ u u' C' Cl hCl hH Z
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hH
  obtain ⟨-, -, hmf, -, hlogf, -, -, -, -, -, hlrd, hg1, hg1b, -, -, -, -, -, hv, -, -, -, -, -, -⟩ := hS0
  have hr : 1 ≤ D.R.rS := hSt.1
  obtain ⟨-, -, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D

  set b := large₂.sc.b with hbdef
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hbexp : b = Real.exp large₂.sc.L := rfl
  have hrd2 : 2 ≤ D.host.rdE := by
    have : D.host.v = D.host.rdE / 2 := rfl
    linarith
  have hrdb : D.host.rdE ≤ b := by
    have hlog : Real.log D.host.rdE ≤ large₂.sc.L := by
      have : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self hL.le hCl
      linarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr hlog
      _ = b := hbexp.symm
  have hb2 : 2 ≤ b := hrd2.trans hrdb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm4 : 4 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf

  have hk : (D.R.k : ℝ) ≤ b ^ (|Cg| / 8) := le_rpow_abs_div_eight_of_mul_pow_le _ _ _ _ (Nat.cast_nonneg _) hb1 hg1 hg1b
  have hsq : D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) hrdb (by norm_num)
  have hbase : 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ (|Cg| / 8 + 3 / 2) := by
    have e : b ^ (|Cg| / 8 + 3 / 2) = b ^ (1 : ℝ) * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, Real.rpow_one]
    have h0 : 0 ≤ D.host.rdE ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h0' : 0 ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
    have h0'' : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg hb0.le _
    calc 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b * b ^ (|Cg| / 8) * D.host.rdE ^ ((1 : ℝ) / 2) := by
          gcongr
      _ ≤ b * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by gcongr
  have hcls := classNumber_le D b hb1 hrdb hf1 hr hlogf
  have h18 : (2 : ℝ) ^ D.R.f * 9 ^ D.R.f ≤ b ^ ((5 : ℝ) * D.R.f) := by
    rw [← mul_pow, Real.rpow_mul hb0.le, Real.rpow_natCast]
    apply pow_le_pow_left₀ (by norm_num)
    have : (2 : ℝ) ^ (5 : ℝ) ≤ b ^ (5 : ℝ) := Real.rpow_le_rpow (by norm_num) hb2 (by norm_num)
    have h32 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    linarith

  set e1 : ℝ := |Cg| / 8 + 3 / 2 with he1
  have he1n : 0 ≤ e1 := by positivity
  have hpow : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f ≤ b ^ (e1 * D.R.f) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hprod : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f
      ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := by
    have e : b ^ ((e1 + D.R.m + 5) * D.R.f) = b ^ (e1 * D.R.f) * b ^ ((D.R.m : ℝ) * D.R.f) * b ^ ((5 : ℝ) * D.R.f) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, mul_assoc _ ((2 : ℝ) ^ D.R.f)]
    have hc0 : (0 : ℝ) ≤ classNumber D.host.E := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ D.R.f * 9 ^ D.R.f := by positivity
    gcongr

  have hm1 : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm4
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |Cg| / 8 := by positivity
    linarith
  have hexp : (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have h1 : e1 + D.R.m + 5 ≤ C * D.R.m := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C - (e1 + 6)) (by linarith : (0 : ℝ) ≤ D.R.m),
        mul_nonneg he1n (by linarith : (0 : ℝ) ≤ D.R.m - 1)]
    have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h2 : 1 ≤ C * (D.R.m : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hC1 hm2
    have h3 : e1 + D.R.m + 5 ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) :=
      h1.trans (le_mul_of_one_le_left (by positivity) h2)
    calc (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) * D.R.f :=
          mul_le_mul_of_nonneg_right h3 hf0
      _ = C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by ring
  have hsz := one_le_size D b C Z
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  calc _ ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := hprod
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) * sizeZ D b C Z ^ 4 := by
        have : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ hsz
        have : 0 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_nonneg hb0.le _
        nlinarith

end GlobalTheory.LoopC.SizeQ
