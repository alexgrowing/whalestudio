import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMetricSegmentPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRaiseWeightSegmentSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantWeightShiftAsymptoticLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSAmpDet

theorem chInt_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) (c : ℝ) (u : SmFn p) :
    chInt L D (u.smul c).u = c * chInt L D u.u := by
  simp only [chInt, SmFn.smul, Weight.chernInt_const_mul, mul_finsum]

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem vals_smul (P : Pair p) (u : SmFn p) (t : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul t)) a b g = fun σ y i => vals P a b g σ y i * (Real.exp (-(a * (t * u.u σ y)) / 2) : ℝ) := by
  funext σ y i
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul t) a b).2.2 σ y (g i)).1

theorem vals_zero (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 0)) a b g = vals P a b g := by
  rw [vals_smul]
  funext σ y i
  simp

theorem vals_one (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 1)) a b g = vals (upperParabolic P u) a b g := by
  rw [vals_smul]
  funext σ y i
  rw [one_mul]
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u a b).2.2 σ y (g i)).1.symm

theorem vals_two (P : Pair p) (u : SmFn p) (t t' : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic (upperParabolic P (u.smul t)) (u.smul (t' - t))) a b g = vals (upperParabolic P (u.smul t')) a b g := by
  rw [vals_smul, vals_smul, vals_smul]
  funext σ y i
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end

theorem tendsto_logDet_gram_sub : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  intro hA k _ X _ p D hX hG P hP ω r f hf hli hr u a a' hsp ha ha'
  obtain ⟨s, hs0, hs1, hsd⟩ := GlobalTheory.T.self_intersection_metric_segment_polynomial hA k X p D hX P.L u a a' ha ha'
  set c : ℝ := 2 / ((D + 1).factorial : ℝ) with hc
  let ℓ : ℚ → ℕ → ℝ := fun t m =>
    Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P (u.smul (t : ℝ))) m 1 (f m))).det.re / (m : ℝ) ^ (D + 1)
  have hR := GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative (Polynomial.C c * s) ℓ ?_
  · have hfun : (fun m => ℓ 0 m - ℓ 1 m) = fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1) := by
      funext m
      simp only [ℓ, Rat.cast_zero, Rat.cast_one, vals_zero, vals_one, sub_div]
    have hval : (Polynomial.C c * s).eval 1 - (Polynomial.C c * s).eval 0 = 2 * (a' - a) / (D + 1).factorial := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hs0, hs1, hc]
      ring
    rw [hfun, hval] at hR
    exact hR
  · intro t t' ht0 ht1 ht0' ht1' ε hε
    have hsemi : (upperParabolic P (u.smul (t : ℝ))).L.SemiPos D :=
      GlobalTheory.T.semiPos_raiseWeight_segment_smul k X p D P.L u t (by exact_mod_cast ht0) (by exact_mod_cast ht1) hP hsp
    have hH : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P (u.smul (t : ℝ))).H m 1 := fun m i => by
      rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul (t : ℝ)) m 1).1]
      exact hf m i
    have hrk : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
        (𝓝 (gdeg (upperParabolic P (u.smul (t : ℝ))).L D / D.factorial)) := by
      rw [show (upperParabolic P (u.smul (t : ℝ))).L = up P.L (u.smul (t : ℝ)) from rfl,
        GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L (u.smul (t : ℝ))]
      exact hr
    have hstep := GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le k X p D hX hG (upperParabolic P (u.smul (t : ℝ))) hsemi ω r f hH hli hrk
      (u.smul ((t' : ℝ) - t)) ε hε
    have hch : chInt (upperParabolic P (u.smul (t : ℝ))).L D (u.smul ((t' : ℝ) - t)).u / D.factorial =
        ((t' : ℝ) - t) * (Polynomial.C c * s).derivative.eval (t : ℝ) := by
      rw [chInt_smul, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hsd t, hc,
        Nat.factorial_succ]
      have hf0 : (D.factorial : ℝ) ≠ 0 := by positivity
      show ((t' : ℝ) - t) * chInt (up P.L (u.smul (t : ℝ))) D u.u / D.factorial = _
      push_cast
      field_simp
    filter_upwards [hstep, eventually_ge_atTop 1] with m hm hm1
    have hpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [vals_two, hch] at hm
    simp only [ℓ]
    rw [← sub_div, div_le_iff₀ hpos]
    linarith

end GlobalTheory.HSAmpDet
