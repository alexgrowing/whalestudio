import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogPotentialFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSmoothOffDivisorStatement

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory

theorem exp_one_le_rComp_of_normSec_le_one {X : Type} [TopologicalSpace X] {m : ℕ}
    (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (i : Fin m) (y : X)
    (h : normSec (L i) (s i) y ≤ 1) : Real.exp 1 ≤ rComp L s i y := by
  unfold rComp
  have h0 : 0 ≤ normSec (L i) (s i) y := by unfold normSec; positivity
  have : Real.log (normSec (L i) (s i) y ^ 2) ≤ 0 :=
    Real.log_nonpos (by positivity) (pow_le_one₀ h0 h)
  linarith

theorem poincare_twoSided : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (Kc c : ℝ), IsPotential A K → IsBoundary A L s D → 0 < Kc →
    (∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ →
      ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w, |ddcAt ψ (rComp L s i) z w| ≤ Kc * formAt ψ K z w) →
    (∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w,
      0 ≤ formAt ψ K z w) →
    0 < c → 2 * c * m * Kc ≤ Real.exp 1 → TwoSided A K L s D c := by
  intro e X _ A K m L s D Kc c hK hB hKc hddc hpos hc hcm ψ hψ z hz hzD w
  have hzDi : ∀ i, ψ.symm z ∉ D i := fun i hi => hzD (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hr : ∀ i, Real.exp 1 ≤ rComp L s i (ψ.symm z) := fun i =>
    exp_one_le_rComp_of_normSec_le_one L s i _ ((hB i).2.2.2 _)
  have hr0 : ∀ i, 0 < rComp L s i (ψ.symm z) := fun i => lt_of_lt_of_le (Real.exp_pos 1) (hr i)
  have hk : ContDiffAt ℝ 2 (K.φ (ψ.symm z) ∘ ψ.symm) z :=
    (GlobalTheory.T.potential_smooth_in_chart A K hK ψ hψ z hz).of_le (WithTop.coe_le_coe.2 le_top)
  have hri : ∀ i, ContDiffAt ℝ 2 ((fun i => rComp L s i ∘ ψ.symm) i) z := fun i =>
    (GlobalTheory.T.boundary_potential_smooth_off_divisor A L s D hB i ψ hψ z hz (hzDi i)).of_le (WithTop.coe_le_coe.2 le_top)
  have hcalc := GlobalTheory.T.levi_form_log_potential_formula (K.φ (ψ.symm z) ∘ ψ.symm) (fun i => rComp L s i ∘ ψ.symm) c z w hk
    hri hr0
  have hβ : formAt ψ (poincarePot K L s c) z w = formAt ψ K z w
      + c * ∑ i, (gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2
        - ddcAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z)) := hcalc
  have ha : 0 ≤ formAt ψ K z w := hpos ψ hψ z hz w
  have hterm : ∀ i, |ddcAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z)|
      ≤ Kc * formAt ψ K z w / Real.exp 1 := by
    intro i
    rw [abs_div, abs_of_pos (hr0 i), div_le_div_iff₀ (hr0 i) (Real.exp_pos 1)]
    have h1 := hddc i ψ hψ z hz hzD w
    have hKa : 0 ≤ Kc * formAt ψ K z w := mul_nonneg hKc.le ha
    calc |ddcAt ψ (rComp L s i) z w| * Real.exp 1 ≤ Kc * formAt ψ K z w * Real.exp 1 := by
          gcongr
      _ ≤ Kc * formAt ψ K z w * rComp L s i (ψ.symm z) := by gcongr; exact hr i
  have hsum : |∑ i, ddcAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z)|
      ≤ m * (Kc * formAt ψ K z w / Real.exp 1) := by
    calc _ ≤ ∑ i, |ddcAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, Kc * formAt ψ K z w / Real.exp 1 := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp
  have hhalf : c * (m * (Kc * formAt ψ K z w / Real.exp 1)) ≤ formAt ψ K z w / 2 := by
    rw [show c * (m * (Kc * formAt ψ K z w / Real.exp 1))
        = (2 * c * m * Kc) * formAt ψ K z w / (2 * Real.exp 1) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hcm ha]
  have hcs : |c * ∑ i, ddcAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z)|
      ≤ formAt ψ K z w / 2 := by
    rw [abs_mul, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left hsum hc.le).trans hhalf
  rw [Finset.sum_sub_distrib, mul_sub] at hβ
  have h2 := abs_le.1 hcs
  constructor
  · linarith
  · linarith

end GlobalTheory
