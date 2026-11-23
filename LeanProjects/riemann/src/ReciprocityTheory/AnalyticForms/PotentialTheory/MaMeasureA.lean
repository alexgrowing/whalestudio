import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix

noncomputable section

theorem leviC_conj_of_symm {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a b : Fin e → ℂ) :
    starRingEnd ℂ (leviC H a b) = leviC H b a := by
  simp only [leviC, map_div₀, map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hs b a, hs (I • b) (I • a), hs b (I • a), hs (I • b) a]
  push_cast
  ring

theorem leviC_self_of_symm {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a : Fin e → ℂ) :
    leviC H a a = (((H a a + H (I • a) (I • a)) / 4 : ℝ) : ℂ) := by
  simp only [leviC]
  rw [hs a (I • a), sub_self]
  push_cast
  ring

theorem hessC_posSemidef_of_levi {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hl : ∀ w, 0 ≤ levi f z w) : (hessC f z).PosSemidef := by
  have hH := hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v := fun v w => hH v w
  have hM : ∀ i j, hessC f z i j =
      leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := hessC_eq_leviC f z
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun i j => ?_) fun x => ?_
  · rw [hM, hM]
    exact leviC_conj_of_symm _ hs _ _
  · have h1 : ∀ i, ∑ j, hessC f z i j * x j =
        leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (star x) := by
      intro i
      rw [← leviC_conj_of_symm _ hs (star x) (Pi.single i 1),
        ← sum_mul_leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (Pi.single i 1), map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM, map_mul, leviC_conj_of_symm _ hs]
      simp [mul_comm]
    have h2 : star x ⬝ᵥ (hessC f z *ᵥ x) =
        leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (star x) := by
      rw [← sum_mul_leviC (fderiv ℝ (fderiv ℝ f) z) (star x) (star x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h1 i]
      rfl
    rw [h2, leviC_self_of_symm _ hs]
    exact_mod_cast hl (star x)

theorem pot_contDiffAt_two {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | norm_num)

theorem hessC_locPot_posSemidef {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (hPsh : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) :
    (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef := by
  exact hessC_posSemidef_of_levi _ y (pot_contDiffAt_two hP _ j hy (P.mem_U _))
    (fun w => hPsh _ j y ⟨hy, P.mem_U _⟩ w)

theorem locDens_nonneg_of_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y
    (fun i => hessC_locPot_posSemidef (hΦ i) (hPsh i) j hy)

theorem locDens_le_add {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Θ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPsh A (Θ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y ≤ locDens A (fun i => Φ i + Θ i) j y := by
  unfold locDens maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _
    (fun k => hessC_locPot_posSemidef (hΦ k) (hΦp k) j hy) fun k => ?_) (by positivity)
  show (hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y -
    hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef
  rw [ReciprocityTheory.AnForm.A.hessC_add (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
    (fun y' => (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y (pot_contDiffAt_two (hΦ k) _ j hy ((Φ k).mem_U _))
    (pot_contDiffAt_two (hΘ k) _ j hy ((Θ k).mem_U _)), add_sub_cancel_left]
  exact hessC_locPot_posSemidef (hΘ k) (hΘp k) j hy

end

end ReciprocityTheory.AnForm.M
