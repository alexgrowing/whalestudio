import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per

namespace GlobalTheory.Per.Val

variable {l : ℕ} [Fact l.Prime]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in

theorem _root_.GlobalTheory.Per.Val.exists_norm_eq (x : _root_.Formalism.BasicNotions.Loc.Om l) (hx : x ≠ 0) :
    ∃ q : ℚ, ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hi hx
  have hn : (minpoly ℚ_[l] x).natDegree ≠ 0 := (minpoly.natDegree_pos hi).ne'
  refine ⟨((minpoly ℚ_[l] x).coeff 0).valuation / (minpoly ℚ_[l] x).natDegree, ?_⟩
  have h1 : ‖x‖ = ‖(minpoly ℚ_[l] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[l] x).natDegree : ℝ)) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) x
  rw [h1, Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg l)]
  congr 1
  have hn' : ((minpoly ℚ_[l] x).natDegree : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.mem_OL_iff (LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  haveI := LL.2
  unfold _root_.Formalism.BasicNotions.Loc.OL
  rw [mem_integralClosure_iff]
  have hK : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hnorm : ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = spectralValue (minpoly ℚ_[l] x) := by
    rw [IntermediateField.minpoly_eq x]; rfl
  rw [hnorm, spectralValue_le_one_iff (minpoly.monic hK)]
  constructor
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, coeff_map]
    simpa using PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hK)
    refine ⟨q, hm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, ← eval₂_map, hq]
    exact minpoly.aeval ℚ_[l] x

open Classical in

def vf (x : Om l) : WithTop ℚ := if h : x = 0 then ⊤ else ((exists_norm_eq x h).choose : ℚ)

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem exists_rat_vf_eq_norm_eq_rpow_of_ne_zero {x : _root_.Formalism.BasicNotions.Loc.Om l} (hx : x ≠ 0) :
    ∃ q : ℚ, _root_.GlobalTheory.Per.Val.vf x = q ∧ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) :=
  ⟨_, by simp [_root_.GlobalTheory.Per.Val.vf, hx],
    (_root_.GlobalTheory.Per.Val.exists_norm_eq x hx).choose_spec⟩

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem prime_rpow_neg_le_iff (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) ≤ (l : ℝ) ^ (-(b : ℝ)) ↔ b ≤ a := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  rw [Real.rpow_le_rpow_left_iff hl, neg_le_neg_iff]
  exact_mod_cast Iff.rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
private theorem prime_rpow_neg_inj (a b : ℚ) :
    (l : ℝ) ^ (-(a : ℝ)) = (l : ℝ) ^ (-(b : ℝ)) ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm ((prime_rpow_neg_le_iff b a).1 h.ge) ((prime_rpow_neg_le_iff a b).1 h.le)
  · rintro rfl; rfl

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_eq_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    _root_.GlobalTheory.Per.Val.vf x = (q : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf, dif_pos, norm_zero, WithTop.top_ne_coe, false_iff]
    exact (Real.rpow_pos_of_pos hl _).ne
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_eq_coe, prime_rpow_neg_inj]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_zero : _root_.GlobalTheory.Per.Val.vf (0 : _root_.Formalism.BasicNotions.Loc.Om l) = ⊤ := by
  simp [_root_.GlobalTheory.Per.Val.vf]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.le_vf_iff (x : _root_.Formalism.BasicNotions.Loc.Om l) (q : ℚ) :
    (q : WithTop ℚ) ≤ _root_.GlobalTheory.Per.Val.vf x ↔ ‖x‖ ≤ (l : ℝ) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  by_cases hx : x = 0
  · subst hx
    simp only [_root_.GlobalTheory.Per.Val.vf_zero, le_top, norm_zero, true_iff]
    exact (Real.rpow_pos_of_pos hl _).le
  · obtain ⟨a, ha, hn⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
    rw [ha, hn, WithTop.coe_le_coe, prime_rpow_neg_le_iff]

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_mul (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    _root_.GlobalTheory.Per.Val.vf (x * y) =
      _root_.GlobalTheory.Per.Val.vf x + _root_.GlobalTheory.Per.Val.vf y := by
  by_cases hx : x = 0
  · simp [hx, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hy : y = 0
  · simp [hy, _root_.GlobalTheory.Per.Val.vf_zero]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [ha, hb, ← WithTop.coe_add, _root_.GlobalTheory.Per.Val.vf_eq_iff, norm_mul, hna, hnb,
    ← Real.rpow_add hl]
  push_cast
  ring_nf

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_add (x y : _root_.Formalism.BasicNotions.Loc.Om l) :
    min (_root_.GlobalTheory.Per.Val.vf x) (_root_.GlobalTheory.Per.Val.vf y) ≤
      _root_.GlobalTheory.Per.Val.vf (x + y) := by
  by_cases hxy : x + y = 0
  · simp [hxy, _root_.GlobalTheory.Per.Val.vf_zero]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha, hna⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hx
  obtain ⟨b, hb, hnb⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hy
  obtain ⟨c, hc, hnc⟩ := exists_rat_vf_eq_norm_eq_rpow_of_ne_zero hxy
  rw [ha, hb, hc, ← WithTop.coe_min, WithTop.coe_le_coe]
  have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
  rw [hna, hnb, hnc] at hmax
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    rw [max_eq_left ((prime_rpow_neg_le_iff b a).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax
  · rw [min_eq_right h]
    rw [max_eq_right ((prime_rpow_neg_le_iff a b).2 h), prime_rpow_neg_le_iff] at hmax
    exact hmax

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_one : _root_.GlobalTheory.Per.Val.vf (1 : _root_.Formalism.BasicNotions.Loc.Om l) = 0 := by
  have := (_root_.GlobalTheory.Per.Val.vf_eq_iff (1 : _root_.Formalism.BasicNotions.Loc.Om l) 0).2 (by simp)
  exact_mod_cast this

open Polynomial in
variable {l : ℕ} [Fact l.Prime] in
theorem _root_.GlobalTheory.Per.Val.vf_l : _root_.GlobalTheory.Per.Val.vf ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = 1 := by
  have h : ‖((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-((1 : ℚ) : ℝ)) := by
    have : ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Om l) = algebraMap ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l) (l : ℚ_[l]) := by simp
    rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
    simp [Real.rpow_neg_one]
  exact_mod_cast (_root_.GlobalTheory.Per.Val.vf_eq_iff _ 1).2 h

def vOm (l : ℕ) [Fact l.Prime] : AddValuation (Om l) (WithTop ℚ) :=
  AddValuation.of vf vf_zero vf_one vf_add vf_mul

end GlobalTheory.Per.Val

namespace GlobalTheory.Per

end GlobalTheory.Per
