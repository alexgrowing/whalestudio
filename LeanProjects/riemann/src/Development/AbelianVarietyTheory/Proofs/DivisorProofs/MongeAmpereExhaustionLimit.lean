import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory

theorem locDens_eq_of_eq_add_const_on {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (B : FinHolAtlas n Y) (Φ Φ' : LocPot Y) (j : Fin B.n)
    (T : Set Y) (hT : IsOpen T) (c : ℝ) (hc : ∀ x, ∀ y ∈ T, Φ.φ x y = Φ'.φ x y + c)
    (w : Fin n → ℂ) (hw : w ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' T) :
    locDens B (fun _ => Φ) j w = locDens B (fun _ => Φ') j w := by
  have hopen : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' T) :=
    (B.chart j).isOpen_inter_preimage_symm hT
  set x := (B.chart j).symm w
  have hev : (fun y' => Φ.φ x ((B.chart j).symm y')) =ᶠ[nhds w]
      fun y' => Φ'.φ x ((B.chart j).symm y') + c := by
    filter_upwards [hopen.mem_nhds hw] with y' hy'
    exact hc x _ hy'.2
  have h1 : fderiv ℝ (fun y' => Φ.φ x ((B.chart j).symm y')) =ᶠ[nhds w]
      fderiv ℝ (fun y' => Φ'.φ x ((B.chart j).symm y')) := by
    have e1 := hev.fderiv (𝕜 := ℝ)
    have e2 : (fderiv ℝ fun y' => Φ'.φ x ((B.chart j).symm y') + c) =
        fderiv ℝ (fun y' => Φ'.φ x ((B.chart j).symm y')) := funext fun _ => fderiv_add_const c
    rw [e2] at e1
    exact e1
  have h2 := h1.fderiv_eq (𝕜 := ℝ)
  unfold locDens maDens hessC
  simp only [x] at h2
  beta_reduce
  simp only [h2]

end GlobalTheory

namespace GlobalTheory

theorem chartSumInt_lt_top_of_monotone_limit : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (P : LocPot X)
    (Ψ : ℕ → LocPot X) (O : ℕ → Set X) (a : ℕ → ℝ) (G : Set Y) (g : Y → ℝ≥0∞) (C : ℝ≥0∞),
    (∀ R, IsPotential A (Ψ R)) → (∀ R, IsOpen (O R)) → Monotone O →
    (∀ R x, ∀ y ∈ O R, (Ψ R).φ x y = P.φ x y + a R) → (∀ y ∈ G, ∃ R, μ y ∈ O R) →
    (∀ [MeasurableSpace Y] [BorelSpace Y], Measurable g) → C < ∞ →
    (∀ R, chartSumInt B ((Ψ R).pullback μ hμ.1) Set.univ g ≤ C) →
    chartSumInt B (P.pullback μ hμ.1) G g < ∞ := by
  intro d X _ A n Y _ B μ hμ P Ψ O a G g C _ hO hmono hagree hG _ hC hbound
  have hchart : ∀ j : Fin B.n, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' G,
      g ((B.chart j).symm w) * ‖locDens B (fun _ => P.pullback μ hμ.1) j w‖ₑ ≤ C := by
    intro j
    set T : ℕ → Set (Fin n → ℂ) := fun R => (B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' O R)
      with hTdef
    have hTmono : Monotone T := fun R R' h w hw => ⟨hw.1, hmono h hw.2⟩
    have hsub : (B.chart j).target ∩ (B.chart j).symm ⁻¹' G ⊆ ⋃ R, T R := by
      intro w hw
      obtain ⟨R, hR⟩ := hG _ hw.2
      exact Set.mem_iUnion.2 ⟨R, hw.1, hR⟩
    calc ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' G,
          g ((B.chart j).symm w) * ‖locDens B (fun _ => P.pullback μ hμ.1) j w‖ₑ
        ≤ ∫⁻ w in ⋃ R, T R,
          g ((B.chart j).symm w) * ‖locDens B (fun _ => P.pullback μ hμ.1) j w‖ₑ :=
          lintegral_mono_set hsub
      _ = ⨆ R, ∫⁻ w in T R,
          g ((B.chart j).symm w) * ‖locDens B (fun _ => P.pullback μ hμ.1) j w‖ₑ :=
          setLIntegral_iUnion_of_directed _ hTmono.directed_le
      _ ≤ C := by
        refine iSup_le fun R => ?_
        have hTopen : IsOpen (T R) :=
          (B.chart j).isOpen_inter_preimage_symm ((hO R).preimage hμ.1)
        have heq : ∫⁻ w in T R,
            g ((B.chart j).symm w) * ‖locDens B (fun _ => P.pullback μ hμ.1) j w‖ₑ =
            ∫⁻ w in T R,
            g ((B.chart j).symm w) * ‖locDens B (fun _ => (Ψ R).pullback μ hμ.1) j w‖ₑ := by
          refine setLIntegral_congr_fun hTopen.measurableSet ?_
          intro w hw
          simp only
          rw [locDens_eq_of_eq_add_const_on B ((Ψ R).pullback μ hμ.1) (P.pullback μ hμ.1) j
            (μ ⁻¹' O R) ((hO R).preimage hμ.1) (a R)
            (fun x y hy => hagree R (μ x) (μ y) hy) w hw]
        rw [heq]
        calc ∫⁻ w in T R,
              g ((B.chart j).symm w) * ‖locDens B (fun _ => (Ψ R).pullback μ hμ.1) j w‖ₑ
            ≤ ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' Set.univ,
              g ((B.chart j).symm w) * ‖locDens B (fun _ => (Ψ R).pullback μ hμ.1) j w‖ₑ :=
              lintegral_mono_set (fun w hw => ⟨hw.1, Set.mem_univ _⟩)
          _ ≤ chartSumInt B ((Ψ R).pullback μ hμ.1) Set.univ g := by
              unfold chartSumInt
              exact Finset.single_le_sum (f := fun j => ∫⁻ w in (B.chart j).target ∩
                (B.chart j).symm ⁻¹' Set.univ,
                g ((B.chart j).symm w) * ‖locDens B (fun _ => (Ψ R).pullback μ hμ.1) j w‖ₑ)
                (fun _ _ => zero_le') (Finset.mem_univ j)
          _ ≤ C := hbound R
  calc chartSumInt B (P.pullback μ hμ.1) G g ≤ ∑ _j : Fin B.n, C :=
        Finset.sum_le_sum fun j _ => hchart j
    _ = (B.n : ℝ≥0∞) * C := by simp
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hC

end GlobalTheory
