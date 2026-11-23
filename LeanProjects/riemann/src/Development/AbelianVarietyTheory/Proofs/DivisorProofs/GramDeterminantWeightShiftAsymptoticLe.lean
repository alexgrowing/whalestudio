import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantJensenChangeOfWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoBergmanMeasureChernFormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem gram_det_up_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX hG P hL ω r f hf hli hr u ε hε
  have hcomp : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hcont : ∀ σ, Continuous (u.u σ) := fun σ =>
    continuous_iff_continuousAt.2 fun y => (u.cInf σ y).continuousAt
  have hT := GlobalTheory.T.tendsto_bergmanMeasure_chernForm_pow k X p D hX hG P hL ω r f hf hli hr u.u hcont
  have hev : ∀ᶠ m : ℕ in atTop, (∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      / (m : ℝ) ^ D < chInt P.L D u.u / D.factorial + ε :=
    hT (Iio_mem_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  obtain ⟨hF, hPD, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  haveI : Finite (k →+* ℂ) := hF.finite
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  have hB : ∀ σ, ∃ C : ℝ, ∀ y, |u.u σ y| ≤ C := fun σ => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont σ).continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  choose C hC using hB
  set w : ∀ σ, CxPts p σ → ℝ := fun σ y => (((m : ℤ) : ℝ)) * u.u σ y with hw
  have hwm : ∀ σ, Measurable (w σ) := fun σ => (continuous_const.mul (hcont σ)).measurable
  have hwb : ∀ σ y, |w σ y| ≤ (m : ℝ) * ∑ τ, |C τ| := fun σ y => by
    simp only [hw, Int.cast_natCast, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
    exact (hC σ y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |C τ|) (fun τ _ => abs_nonneg _) (Finset.mem_univ σ)))
  obtain ⟨-, -, hJ⟩ := GlobalTheory.T.gramDeterminant_jensen_change_of_weight (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m)) (fun σ => (ω σ).meas)
    (vals P m 1 (f m)) hF hPD w _ hwm hwb
  have hnew : (fun σ y i => vals P m 1 (f m) σ y i * ((Real.exp (-(w σ y) / 2) : ℝ) : ℂ))
      = vals (upperParabolic P u) m 1 (f m) := by
    funext σ y i
    simp only [vals, hw]
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y (f m i)).1]
  rw [hnew] at hJ
  have hsum : (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      = (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by
    rw [mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw, Int.cast_natCast]
    ring
  rw [hsum] at hJ
  have hmpos : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast hm1) D
  rw [div_lt_iff₀ hmpos] at hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 := mul_le_mul_of_nonneg_left hm.le hm0
  calc _ ≤ (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by linarith
    _ ≤ _ := h2
    _ = _ := by ring

end GlobalTheory.HSAmp
