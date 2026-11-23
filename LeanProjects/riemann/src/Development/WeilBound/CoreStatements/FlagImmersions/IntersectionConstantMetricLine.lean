import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_const_mul (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    refine congrArg _ (funext fun y => ?_)
    rw [← smul_eq_mul, smul_finsum]
    refine finsum_congr (fun w => ?_)
    rw [smul_finsum]
    refine finsum_congr (fun hw => ?_)
    unfold sheetDensity
    split_ifs <;> simp [mul_assoc]
  · simp

theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  simpa using ptsIntegral_const_mul P φ (fun _ => (1 : ℝ)) c

theorem smooth_constLine (c : ℝ) :
    IsSmoothHerm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) := by
  unfold IsSmoothHerm HermLine.ofWeight
  exact contDiffOn_const

theorem intersection_constant_metric_line : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  intro II hII K _ ι _ P e L c hP hL
  have hA : IsSmoothHerm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) :=
    smooth_constLine c
  have hprime : P.IsPrime := hP.2.1.1
  have h1 : (1 : MRing ι) ∉ P := fun h => hprime.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hhom : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    rw [Finset.mem_singleton.1 hm]
    simp
  rw [(hII K ι).2.2 P e L _ 1 (fun _ => 0) hP hL hA (fun k => by simp [HermLine.ofWeight]) hhom h1]
  have hempty : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hW
    rw [Ideal.span_singleton_one, sup_top_eq] at hW
    exact (hW.1.1.ne_top (top_le_iff.1 hW.1.2)).elim
  unfold recR arInt
  simp only [hempty, Set.mem_empty_iff_false, finsum_false, finsum_zero, zero_sub]
  have hln : logNorm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) (1 : MRing ι) = fun _ => c := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  rw [hln, ptsIntegral_const]
  ring

end RootFieldNumerics
