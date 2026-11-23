import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBoundedByPositivePotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSectionSqSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormGradientLeviIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNormLocalFormulaStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

theorem GlobalTheory.PoincareGrad.gradSq_le_exp_mul_form : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsPotential A K → IsPosPot A K → IsBoundary A L s D → ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ D i → ∀ w, gradSqAt ψ (rComp L s i) z w ≤ C * Real.exp (rComp L s i (ψ.symm z)) * formAt ψ K z w := by
  intro e X _ _ _ A K m L s D hK hKpos hB
  have hcmp := @GlobalTheory.T.form_bounded_by_positive_potential
  obtain ⟨C0, hC0, hK0⟩ := hcmp A K K hK hK hKpos
  have hKnn : ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w,
      0 ≤ formAt ψ K z w := fun ψ hψ z hz w => by
    have h1 := hK0 ψ hψ z hz w
    have h2 := abs_nonneg (formAt ψ K z w)
    exact nonneg_of_mul_nonneg_right (h2.trans h1) hC0
  have h1 : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ →
      ∀ z ∈ ψ.target, ∀ w, |formAt ψ (LocPot.ofFun (fun y => normSec (L i) (s i) y ^ 2)) z w|
        ≤ C * formAt ψ K z w := fun i =>
    hcmp A _ K (isPotential_ofFun A _ (GlobalTheory.T.norm_section_sq_smooth A (L i) (s i) (hB i).1 (hB i).2.1)) hK hKpos
  have h2 : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ →
      ∀ z ∈ ψ.target, ∀ w, |formAt ψ (L i) z w| ≤ C * formAt ψ K z w := fun i =>
    hcmp A (L i) K (hB i).1 hK hKpos
  choose C1 hC1 hb1 using h1
  choose C2 hC2 hb2 using h2
  have hCpos : 0 < ∑ j, (C1 j + C2 j) + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => (add_pos (hC1 j) (hC2 j)).le) one_pos
  refine ⟨∑ j, (C1 j + C2 j) + 1, hCpos, ?_⟩
  intro i ψ hψ z hz hzD w
  set x := ψ.symm z with hx
  set N : (Fin e → ℂ) → ℝ := fun y => normSec (L i) (s i) (ψ.symm y) ^ 2 with hN
  obtain ⟨hh, hh0, hev⟩ := GlobalTheory.T.section_norm_local_formula A L s D hB i ψ hψ z hz hzD
  have hΦ : ContDiffAt ℝ 2 ((L i).φ x ∘ ψ.symm) z :=
    (GlobalTheory.T.potential_smooth_in_chart A (L i) (hB i).1 ψ hψ z hz).of_le (WithTop.coe_le_coe.2 le_top)
  have key := GlobalTheory.T.log_norm_gradient_levi_identity _ _ N z w hh hh0 hΦ hev

  have hNpos : 0 < N z := by
    have h3 : N z = ‖s i x x‖ ^ 2 * Real.exp (-2 * (L i).φ x x) := hev.eq_of_nhds
    rw [h3]; positivity

  have hgrad : gradSqAt ψ (rComp L s i) z w = Real.exp (rComp L s i x - Real.exp 1) *
      (ddcAt ψ (fun y => normSec (L i) (s i) y ^ 2) z w + N z * formAt ψ (L i) z w) := by
    have hr : rComp L s i x - Real.exp 1 = -Real.log (N z) := by
      simp only [rComp]; rw [show N z = normSec (L i) (s i) x ^ 2 from rfl]; ring
    have hc : (rComp L s i ∘ ψ.symm) = fun y => Real.exp 1 - Real.log (N y) := rfl
    rw [hr, Real.exp_neg, Real.exp_log hNpos]
    unfold gradSqAt ddcAt formAt
    rw [hc]
    have hc2 : ((fun y => normSec (L i) (s i) y ^ 2) ∘ ψ.symm) = N := rfl
    rw [hc2]
    have hNne : N z ≠ 0 := hNpos.ne'
    have hk : 1 / Real.pi * levi N z w + N z * (2 / Real.pi * levi ((L i).φ x ∘ ψ.symm) z w) =
        1 / Real.pi * (((fderiv ℝ (fun y => Real.exp 1 - Real.log (N y)) z w) ^ 2 +
          (fderiv ℝ (fun y => Real.exp 1 - Real.log (N y)) z (Complex.I • w)) ^ 2) / 4 * N z) := by
      rw [key]; ring
    rw [hk]
    field_simp
  have hddc : ddcAt ψ (fun y => normSec (L i) (s i) y ^ 2) z w
      = formAt ψ (LocPot.ofFun (fun y => normSec (L i) (s i) y ^ 2)) z w / 2 := by
    simp only [ddcAt, formAt, LocPot.ofFun]; ring
  have hN1 : N z ≤ 1 := by
    have h4 := (hB i).2.2.2 x
    have h5 : 0 ≤ normSec (L i) (s i) x := by unfold normSec; positivity
    simp only [hN]
    nlinarith
  set F := formAt ψ K z w
  have hF := hKnn ψ hψ z hz w
  have b1 := hb1 i ψ hψ z hz w
  have b2 := hb2 i ψ hψ z hz w
  have hsum : C1 i + C2 i ≤ ∑ j, (C1 j + C2 j) + 1 := by
    have := Finset.single_le_sum (f := fun j => C1 j + C2 j)
      (fun j _ => (add_pos (hC1 j) (hC2 j)).le) (Finset.mem_univ i)
    linarith
  have hbr : ddcAt ψ (fun y => normSec (L i) (s i) y ^ 2) z w + N z * formAt ψ (L i) z w
      ≤ (∑ j, (C1 j + C2 j) + 1) * F := by
    rw [hddc]
    have e1 := le_abs_self (formAt ψ (LocPot.ofFun (fun y => normSec (L i) (s i) y ^ 2)) z w)
    have e2 : N z * formAt ψ (L i) z w ≤ |formAt ψ (L i) z w| := by
      calc N z * formAt ψ (L i) z w ≤ N z * |formAt ψ (L i) z w| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hNpos.le
        _ ≤ 1 * |formAt ψ (L i) z w| := mul_le_mul_of_nonneg_right hN1 (abs_nonneg _)
        _ = _ := one_mul _
    have e3 : (C1 i + C2 i) * F ≤ (∑ j, (C1 j + C2 j) + 1) * F := mul_le_mul_of_nonneg_right hsum hF
    nlinarith [hC1 i]
  have hE : Real.exp (rComp L s i x - Real.exp 1) ≤ Real.exp (rComp L s i x) :=
    Real.exp_le_exp.2 (by linarith [Real.exp_pos 1])
  rw [hgrad]
  calc Real.exp (rComp L s i x - Real.exp 1) *
        (ddcAt ψ (fun y => normSec (L i) (s i) y ^ 2) z w + N z * formAt ψ (L i) z w)
      ≤ Real.exp (rComp L s i x - Real.exp 1) * ((∑ j, (C1 j + C2 j) + 1) * F) :=
        mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
    _ ≤ Real.exp (rComp L s i x) * ((∑ j, (C1 j + C2 j) + 1) * F) :=
        mul_le_mul_of_nonneg_right hE (mul_nonneg hCpos.le hF)
    _ = (∑ j, (C1 j + C2 j) + 1) * Real.exp (rComp L s i x) * F := by ring
