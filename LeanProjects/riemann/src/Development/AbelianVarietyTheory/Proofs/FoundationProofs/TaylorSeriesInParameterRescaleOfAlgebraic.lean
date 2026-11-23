import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.SerTransport

open PowerSeries

theorem taylorCoeff_add_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z + G z) n = coef1 F n + coef1 G n := by
  simp only [coef1]
  rw [iteratedDeriv_fun_add hF.contDiff.contDiffAt hG.contDiff.contDiffAt, add_div]

theorem taylorCoeff_mul_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z * G z) n =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, coef1 F q.1 * coef1 G q.2 := by
  simp only [coef1]
  rw [iteratedDeriv_fun_mul hF.contDiff.contDiffAt hG.contDiff.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : ((n.choose i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

theorem taylorCoeff_const_function (c : ℂ) (n : ℕ) : coef1 (fun _ => c) n = if n = 0 then c else 0 := by
  simp only [coef1, iteratedDeriv_const]
  split_ifs with h
  · simp [h]
  · simp

theorem taylorCoeff_zero_eq_value (F : ℂ → ℂ) : coef1 F 0 = F 0 := by simp [coef1]

theorem taylorCoeff_scale_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (β : ℂ) (n : ℕ) :
    coef1 (fun z => F (β * z)) n = β ^ n * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_comp_const_mul hF.contDiff]
  simp [mul_div_assoc]

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem coeff_padicTransportSeries (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (n : ℕ) :
    coeff n (GL3Theta.ser1 lam F) = lamC lam (coef1 F n) := by
  simp [GL3Theta.ser1, coef1]

theorem exists_coef {F : ℂ → ℂ} (hF : AlgEnt F) : ∃ a : ℕ → Qbar, ∀ n, coef1 F n = a n :=
  ⟨fun n => ⟨_, hF.2 n⟩, fun _ => rfl⟩

theorem padicTransportSeries_add (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z + G z) ∧
      GL3Theta.ser1 lam (fun z => F z + G z) = GL3Theta.ser1 lam F + GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z + G z) n = ((a n + b n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_add_entire hF.1 hG.1, ha, hb]; rfl
  refine ⟨⟨hF.1.add hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [map_add, coeff_padicTransportSeries, e, ha, hb, lamC_coe]

theorem padicTransportSeries_mul (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z * G z) ∧
      GL3Theta.ser1 lam (fun z => F z * G z) = GL3Theta.ser1 lam F * GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z * G z) n =
      ((∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, a q.1 * b q.2 : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_mul_entire hF.1 hG.1]
    simp [ha, hb]
  refine ⟨⟨hF.1.mul hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [coeff_mul, coeff_padicTransportSeries, e, ha, hb, lamC_coe, map_sum, map_mul]

theorem padicTransportSeries_const (lam : Qbar →+* ℂ_[p]) {c : ℂ} (hc : c ∈ Qbar) :
    AlgEnt (fun _ => c) ∧ GL3Theta.ser1 lam (fun _ => c) = C (lamC lam c) := by
  refine ⟨⟨differentiable_const c, fun n => ?_⟩, ?_⟩
  · rw [taylorCoeff_const_function]
    split_ifs
    exacts [hc, zero_mem _]
  · ext n
    rw [coeff_padicTransportSeries, taylorCoeff_const_function, coeff_C]
    split_ifs
    · rfl
    · exact (lamC_coe lam 0).trans (map_zero lam)

theorem taylorSeriesInParameter_rescale_of_algebraic (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) {β : ℂ} (hβ : β ∈ Qbar) :
    AlgEnt (fun z => F (β * z)) ∧
      GL3Theta.ser1 lam (fun z => F (β * z)) = rescale (lamC lam β) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, rfl⟩ : ∃ b : Qbar, (b : ℂ) = β := ⟨⟨β, hβ⟩, rfl⟩
  have e : ∀ n, coef1 (fun z => F (b * z)) n = ((b ^ n * a n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_scale_entire hF.1, ha]
    simp
  refine ⟨⟨hF.1.comp (by fun_prop), fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [coeff_rescale, coeff_padicTransportSeries, e, ha, lamC_coe, map_pow, map_mul]

theorem const_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    constantCoeff (f.subst a : PowerSeries ℂ_[p]) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

theorem one_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    coeff 1 (f.subst a : PowerSeries ℂ_[p]) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, const_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

variable (g : GL3Theta.G1 p)

theorem const_l : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_Cl (c : ℂ_[p]) : constantCoeff (C c * g.l) = 0 := by
  rw [map_mul, const_l, mul_zero]

theorem atU_eq (F : ℂ → ℂ) : g.atU F =
    subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l : PowerSeries ℂ_[p]) (GL3Theta.ser1 g.lam F) := rfl

theorem mulBy_X (c : ℂ_[p]) : (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
    subst (C c * g.l : PowerSeries ℂ_[p]) g.ex := by
  have : g.lg (GL3Theta.Xv ()) = g.l := X_subst g.l
  rw [GL3Theta.G1.mulBy, this]
  rfl

theorem transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), (∀ F G : ℂ → ℂ, AlgEnt F → AlgEnt G → (AlgEnt (fun z => F z * G z) ∧ g.atU (fun z => F z * G z) = g.atU F * g.atU G) ∧ (AlgEnt (fun z => F z + G z) ∧ g.atU (fun z => F z + G z) = g.atU F + g.atU G)) ∧ (∀ c ∈ Qbar, AlgEnt (fun _ => c) ∧ g.atU (fun _ => c) = PowerSeries.C (lamC g.lam c)) ∧ (∀ F : ℂ → ℂ, AlgEnt F → F 0 ∈ Qbar ∧ PowerSeries.constantCoeff (g.atU F) = lamC g.lam (F 0)) ∧ (g.Ok → ∀ β ∈ Qbar, ∃ h : PowerSeries ℂ_[p], h = (g.mulBy (lamC g.lam β) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧ PowerSeries.constantCoeff h = 0 ∧ PowerSeries.coeff 1 h = lamC g.lam β ∧ ∀ F : ℂ → ℂ, AlgEnt F → AlgEnt (fun z => F (β * z)) ∧ g.atU (fun z => F (β * z)) = PowerSeries.subst h (g.atU F)) := by
  intro p _ g
  have hs := HasSubst.of_constantCoeff_zero' (const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  refine ⟨fun F G hF hG => ⟨⟨(padicTransportSeries_mul g.lam hF hG).1, ?_⟩, (padicTransportSeries_add g.lam hF hG).1, ?_⟩,
    fun c hc => ⟨(padicTransportSeries_const g.lam hc).1, ?_⟩, fun F hF => ⟨taylorCoeff_zero_eq_value F ▸ hF.2 0, ?_⟩, fun hg β hβ => ?_⟩
  · simp only [atU_eq, (padicTransportSeries_mul g.lam hF hG).2, subst_mul hs]
  · simp only [atU_eq, (padicTransportSeries_add g.lam hF hG).2, subst_add hs]
  · rw [atU_eq, (padicTransportSeries_const g.lam hc).2, subst_C]; rfl
  · rw [atU_eq, const_subst (const_Cl g _), ← coeff_zero_eq_constantCoeff_apply, coeff_padicTransportSeries, taylorCoeff_zero_eq_value]
  · set b := lamC g.lam β with hb
    have hbl := HasSubst.of_constantCoeff_zero' (const_Cl g b)
    have he := HasSubst.of_constantCoeff_zero' hg.2.2.1
    have h0 : constantCoeff (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) = 0 := by
      rw [const_subst (const_Cl g b), hg.2.2.1]
    have hh := HasSubst.of_constantCoeff_zero' h0
    refine ⟨subst (C b * g.l : PowerSeries ℂ_[p]) g.ex, (mulBy_X g b).symm, h0, ?_, fun F hF =>
      ⟨(taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).1, ?_⟩⟩
    · have e := congrArg (coeff 1) hg.2.2.2
      rw [one_subst hg.2.2.1, coeff_one_X] at e
      rw [one_subst (const_Cl g b), coeff_C_mul]
      linear_combination b * e
    · have e : subst (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) g.l = C b * g.l := by
        rw [← subst_comp_subst_apply he hbl, hg.2.2.2, subst_X hbl]
      rw [atU_eq, atU_eq, (taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).2, rescale_eq_subst,
        subst_comp_subst_apply (HasSubst.smul_X' _) hs, subst_comp_subst_apply hs hh,
        subst_smul hs, subst_X hs, subst_mul hh, e, subst_C]
      congr 1
      rw [smul_eq_C_mul]
      exact mul_left_comm _ _ _

end GlobalTheory.SerTransport
