import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.NormVal

section General

variable {K : Type*} [Field K]

theorem exists_coe (v : AddValuation K (WithTop ℚ)) {x : K} (hx : x ≠ 0) :
    ∃ r : ℚ, v x = (r : WithTop ℚ) := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  have h' : v x ≠ ⊤ := by
    intro e
    rw [e, top_add] at h
    exact WithTop.top_ne_zero h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h'
  exact ⟨r, hr.symm⟩

end General

open GlobalTheory.Per.Val

open TensorProduct in
private lemma addValuation_pow_mul_pow_div_pow {F : Type*} [Field F]
    (u : AddValuation F (WithTop ℚ)) {π : F} (hu : u π = 1) {x : F} {t : ℚ} (hx : u x = t)
    (b M N : ℕ) : u (x ^ b * π ^ M / π ^ N) = ((b * t + M - N : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_div, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
    AddValuation.map_pow, hx, hu]
  norm_cast
  simp [nsmul_eq_mul]

open TensorProduct in
private lemma le_of_nonneg_imp_nonneg {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ)) {π : F}
    (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y → 0 ≤ w y) {x : F} {t s : ℚ}
    (hvx : v x = t) (hwx : w x = s) : t ≤ s := by
  have hMN : ((t.num.toNat : ℕ) : ℚ) - ((-t.num).toNat : ℕ) = t.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg t.num
  have hbt : (t.den : ℚ) * t = t.num := by rw [mul_comm]; exact Rat.mul_den_eq_num t
  have hy := h (x ^ t.den * π ^ (-t.num).toNat / π ^ t.num.toNat) (by
    rw [addValuation_pow_mul_pow_div_pow v hv hvx]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t.den * t + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ)))
  rw [addValuation_pow_mul_pow_div_pow w hw hwx] at hy
  have hy' : (0 : ℚ) ≤ t.den * s + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ) := by exact_mod_cast hy
  have hd : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  nlinarith

open TensorProduct in
private lemma addValuation_eq_of_nonneg_iff {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ))
    {π : F} (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y ↔ 0 ≤ w y) (x : F) : v x = w x := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff v).mp hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff w).mp hx)
  rw [← ht, ← hs]
  have h1 := le_of_nonneg_imp_nonneg v w hv hw (fun y => (h y).mp) ht.symm hs.symm
  have h2 := le_of_nonneg_imp_nonneg w v hw hv (fun y => (h y).mpr) hs.symm ht.symm
  exact congrArg _ (le_antisymm h1 h2)

open TensorProduct in

theorem _root_.GlobalTheory.HWL.NormVal.locPrime_v_normalised : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), (∀ (x : ↥LL.1) (q : ℚ), P.v LL x = (q : WithTop ℚ) ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-(q : ℝ))) ∧ (∀ (x : ↥LL.1) (q : ℚ), (q : WithTop ℚ) ≤ P.v LL x ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ (l : ℝ) ^ (-(q : ℝ))) ∧ ∀ x : ↥LL.1, x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  intro l _ P LL
  set w : AddValuation (↥LL.1) (WithTop ℚ) :=
    (_root_.GlobalTheory.Per.Val.vOm l).comap (algebraMap (↥LL.1) (_root_.Formalism.BasicNotions.Loc.Om l)) with hwdef
  have hwx : ∀ x : ↥LL.1, w x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x => rfl
  have hw : w (l : ↥LL.1) = 1 := by
    rw [hwx]
    have : ((l : ↥LL.1) : _root_.Formalism.BasicNotions.Loc.Om l) = (l : _root_.Formalism.BasicNotions.Loc.Om l) := by simp
    rw [this]
    exact _root_.GlobalTheory.Per.Val.vf_l
  have hnn : ∀ y : ↥LL.1, 0 ≤ P.v LL y ↔ 0 ≤ w y := by
    intro y
    rw [_root_.Formalism.BasicNotions.LocPrime.v_O, _root_.GlobalTheory.Per.Val.mem_OL_iff, hwx]
    have := _root_.GlobalTheory.Per.Val.le_vf_iff (y : _root_.Formalism.BasicNotions.Loc.Om l) 0
    simp only [Rat.cast_zero, neg_zero, Real.rpow_zero, WithTop.coe_zero] at this
    exact this.symm
  have key : ∀ x : ↥LL.1, P.v LL x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x =>
    (addValuation_eq_of_nonneg_iff (P.v LL) w (P.v_l LL) hw hnn x).trans (hwx x)
  refine ⟨fun x q => ?_, fun x q => ?_, fun x => _root_.GlobalTheory.Per.Val.mem_OL_iff LL x⟩
  · rw [key]; exact _root_.GlobalTheory.Per.Val.vf_eq_iff _ q
  · rw [key]; exact _root_.GlobalTheory.Per.Val.le_vf_iff _ q

end GlobalTheory.HWL.NormVal
