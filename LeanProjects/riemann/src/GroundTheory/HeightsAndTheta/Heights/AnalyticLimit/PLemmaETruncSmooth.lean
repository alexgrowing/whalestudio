import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_add_smul levi_congr)
open ReciprocityTheory.AnForm.A (regMax regMax_thm regMaxLevi_thm)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh pot_contDiffAt_two)

noncomputable section

theorem contDiffAt_regMax_trunc {D : ℕ} {n : WithTop ℕ∞} (hn : n ≤ ∞) {a : (Fin D → ℂ) → ℝ}
    {y : Fin D → ℂ} (c : ℝ) {η : ℝ} (hη : 0 < η) (ha : ContDiffAt ℝ n a y) :
    ContDiffAt ℝ n (fun z => regMax η ![a z, c] - η) y := by
  have hR : ContDiff ℝ n (regMax (ι := Fin 2) η) := ((regMax_thm (Fin 2)).1 η hη).1.of_le hn
  have hin : ContDiffAt ℝ n (fun z => ![a z, c]) y := by
    refine contDiffAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using contDiffAt_const
  exact (hR.comp_contDiffAt y hin).sub contDiffAt_const

theorem levi_regMax_trunc {D : ℕ} {O : Set (Fin D → ℂ)} (hO : IsOpen O) {f a : (Fin D → ℂ) → ℝ}
    {y : Fin D → ℂ} (hy : y ∈ O) (c : ℝ) {η : ℝ} (hη : 0 < η) (hf : ContDiffAt ℝ 2 f y)
    (ha : ContDiffOn ℝ 2 a O) (w : Fin D → ℂ) (h1 : 0 ≤ levi f y w)
    (h2 : 0 ≤ levi (fun z => f z + a z) y w) :
    0 ≤ levi (fun z => f z + (regMax η ![a z, c] - η)) y w := by
  have haAt : ContDiffAt ℝ 2 a y := ha.contDiffAt (hO.mem_nhds hy)
  have hT := contDiffAt_regMax_trunc (WithTop.coe_le_coe.mpr le_top) c hη haAt
  have e1 : levi (fun z => f z + (regMax η ![a z, c] - η)) y w =
      levi f y w + 1 * levi (fun z => regMax η ![a z, c] - η) y w := by
    rw [← levi_add_smul 1 hf hT w]
    simp only [one_mul]
  have e2 : levi (fun z => regMax η ![a z, c] - η) y w =
      levi (fun z => regMax η (fun j => (![a, fun _ => c] : Fin 2 → (Fin D → ℂ) → ℝ) j z)) y w := by
    have : (fun z => regMax η ![a z, c] - η) =
        fun z => regMax η (fun j => (![a, fun _ => c] : Fin 2 → (Fin D → ℂ) → ℝ) j z) + (-η) := by
      funext z
      rw [sub_eq_add_neg]
      congr 2
      funext j
      fin_cases j <;> rfl
    rw [this, levi_add_const]
  have e3 : levi (fun z => f z + a z) y w = levi f y w + 1 * levi a y w := by
    rw [← levi_add_smul 1 hf haAt w]
    simp only [one_mul]
  have hR := regMaxLevi_thm D (Fin 2) η O ![a, fun _ => c] hO hη
    (fun j => by
      fin_cases j
      · exact ha
      · exact contDiffOn_const) y hy w (-levi f y w)
    (fun j => by
      fin_cases j
      · show -levi f y w ≤ levi a y w
        linarith
      · show -levi f y w ≤ levi (fun _ => c) y w
        rw [levi_const]
        linarith)
  rw [e1, e2]
  linarith

theorem trunc_smooth_psh {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) {W : Set X} (hW : IsOpen W) {u : X → ℝ} (hu : A.SmoothOn W u)
    (hnn : FormNonneg A W (potForm Om.pot u)) (c : ℝ) {η : ℝ} (hη : 0 < η) (v : X → ℝ)
    (hvW : ∀ p ∈ W, v p = regMax η ![u p, c] - η)
    (hvC : ∀ p ∉ W, ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ ∃ κ : ℝ, ∀ q ∈ N, v q = κ) :
    A.Smooth v ∧ IsPsh A (potForm Om.pot v) := by

  have hE1 : ∀ j y, y ∈ (A.chart j).target → (A.chart j).symm y ∈ W →
      ∀ᶠ z in 𝓝 y, v ((A.chart j).symm z) = regMax η ![u ((A.chart j).symm z), c] - η := by
    intro j y hy hyW
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hy, hyW⟩] with z hz
    exact hvW _ hz.2

  have hE2 : ∀ j y, y ∈ (A.chart j).target → (A.chart j).symm y ∉ W →
      ∃ κ : ℝ, ∀ᶠ z in 𝓝 y, v ((A.chart j).symm z) = κ := by
    intro j y hy hyW
    obtain ⟨N, hN, hpN, κ, hκ⟩ := hvC _ hyW
    exact ⟨κ, by
      filter_upwards [((A.chart j).isOpen_inter_preimage_symm hN).mem_nhds ⟨hy, hpN⟩] with z hz
      exact hκ _ hz.2⟩
  have hOW : ∀ j, IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) := fun j =>
    (A.chart j).isOpen_inter_preimage_symm hW
  refine ⟨fun j y hy => ?_, fun x j y hy w => ?_⟩
  · refine ContDiffAt.contDiffWithinAt ?_
    by_cases hyW : (A.chart j).symm y ∈ W
    · exact (contDiffAt_regMax_trunc le_rfl c hη
        ((hu j).contDiffAt ((hOW j).mem_nhds ⟨hy.1, hyW⟩))).congr_of_eventuallyEq (hE1 j y hy.1 hyW)
    · obtain ⟨κ, hκ⟩ := hE2 j y hy.1 hyW
      exact contDiffAt_const.congr_of_eventuallyEq hκ
  · have hyU : (A.chart j).symm y ∈ Om.pot.U x := hy.2.1
    have hf := pot_contDiffAt_two Om.isPot x j hy.1 hyU
    have h1 : 0 ≤ levi (Om.pot.φ x ∘ (A.chart j).symm) y w := Om.isPsh x j y ⟨hy.1, hyU⟩ w
    show 0 ≤ levi (fun z => Om.pot.φ x ((A.chart j).symm z) + v ((A.chart j).symm z)) y w
    by_cases hyW : (A.chart j).symm y ∈ W
    · have hcg : (fun z => Om.pot.φ x ((A.chart j).symm z) + v ((A.chart j).symm z)) =ᶠ[𝓝 y]
          fun z => (Om.pot.φ x ∘ (A.chart j).symm) z +
            (regMax η ![(u ∘ (A.chart j).symm) z, c] - η) := by
        filter_upwards [hE1 j y hy.1 hyW] with z hz
        simp only [Function.comp, hz]
      rw [levi_congr hcg]
      exact levi_regMax_trunc (hOW j) ⟨hy.1, hyW⟩ c hη hf
        (contDiffOn_infty.1 (hu j) 2) w h1 (hnn x j y ⟨hy.1, hyW, hyU, Set.mem_univ _⟩ w)
    · obtain ⟨κ, hκ⟩ := hE2 j y hy.1 hyW
      have hcg : (fun z => Om.pot.φ x ((A.chart j).symm z) + v ((A.chart j).symm z)) =ᶠ[𝓝 y]
          fun z => (Om.pot.φ x ∘ (A.chart j).symm) z + κ := by
        filter_upwards [hκ] with z hz
        simp only [Function.comp, hz]
      rw [levi_congr hcg, levi_add_const]
      exact h1

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
