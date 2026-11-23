import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNull
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepE

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem b_step {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
    (hS : SAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n) (hLSE : LSEAll.{u} n)
    (hn : 2 ≤ n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    (T' : ℕ) (hT : n + 1 ≤ T') (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∃ hh : Fin n → ι → Y → ℂ,
      (∀ k, A.IsSec (mu0 + (T' - 1) • L) (hh k) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + (T' - 1) • L) (hh k) y *
          A.sqn L s y ^ (-((T' : ℝ) - 3 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source → f i y = ∑ k, s k i y * hh k i y := by
  classical
  have hT1 : 1 ≤ T' := by omega
  have hT2 : 2 ≤ T' := by omega
  have hMo := isOpen_Mset A (De := De) hD
  obtain ⟨H, hHol, hid, hbd⟩ := bsD_skoda A hS hLSE hn hD hF hX hσ hpos T' hT f hf hint
  have hint' := fun k => bsE_int A hD hF hσ hX T' hT1 H hHol k hbd
  have hex : ∀ k, ∃ G : ι → Y → ℂ, A.IsSec (mu0 + (T' - 1) • L) G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source →
        G i y = bsH (A.Mset w0 s De) (H k) σ w0 (T' - 1) i y := fun k =>
    ext_Mset A hE hD hF _ _ (bsE_sec A hD hF hσ (H k) (hHol k) (T' - 1))
      (bsE_loc A hD hF hσ hX T' hT2 (H k) (hHol k) (hint' k))
  choose G hGs hGeq using hex
  refine ⟨G, fun k => ⟨hGs k, ?_⟩, ?_⟩
  · have hae : ∀ᵐ y ∂A.mu, y ∈ A.Mset w0 s De := by
      rw [ae_iff]; exact mu_compl_Mset A hN hD hF
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    refine lt_of_eq_of_lt (setLIntegral_congr_fun hMo.measurableSet fun y hy => ?_) (hint' k)
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    have : A.nsq (mu0 + (T' - 1) • L) (G k) y =
        A.nsq (mu0 + (T' - 1) • L) (bsH (A.Mset w0 s De) (H k) σ w0 (T' - 1)) y := by
      unfold nsq; rw [hGeq k (A.pick y) y hy (A.mem_pick y)]
    rw [this, mul_assoc]
    rfl
  · intro i y hy
    have hcont : ContinuousOn (fun y => ∑ k, s k i y * G k i y) (A.chart i).source :=
      continuousOn_finsetSum _ fun k _ =>
        (continuousOn_section_chart A (hD.sec_s k) i).mul (continuousOn_section_chart A (hGs k) i)
    have hEq : Set.EqOn (f i) (fun y => ∑ k, s k i y * G k i y)
        ((A.chart i).source ∩ A.Mset w0 s De) := by
      intro x hx
      have hxM := hx.2
      have hp := A.mem_pick x
      have hw : w0 i x ≠ 0 := denominator_ne_zero_on_chart A hD hxM hx.1
      have hσi : σ i x ≠ 0 := bsA_ne_of_tr A hσ.1.2 hxM hx.1 hp (hσ.2 x hxM)
      have hfM := bsA_isSecOn_mono A hf (Set.subset_univ (A.Mset w0 s De))
      have hr1 : f i x / (σ i x * w0 i x ^ T') =
          f (A.pick x) x / (σ (A.pick x) x * w0 (A.pick x) x ^ T') :=
        bsA_tr_ratio A hfM.2 (bsD_denom A hD hσ T').2 hxM hx.1 hp
      have hr2 : ∀ k, s k (A.pick x) x / w0 (A.pick x) x = s k i x / w0 i x := fun k =>
        (bsA_tr_ratio A (bsA_isSecOn_mono A (hD.sec_s k) (Set.subset_univ _)).2
          (bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ _)).2 hxM hx.1 hp).symm
      have hid' := hid ⟨x, hxM⟩
      simp only at hid'
      rw [← hr1] at hid'
      simp_rw [hr2] at hid'
      have hG : ∀ k, G k i x = H k ⟨x, hxM⟩ * (σ i x * w0 i x ^ (T' - 1)) := by
        intro k
        rw [hGeq k i x hxM hx.1]
        simp only [bsH, bsE_ext_mem _ hxM]
      have hpow : w0 i x ^ T' = w0 i x ^ (T' - 1) * w0 i x := by
        rw [← pow_succ, Nat.sub_add_cancel hT1]
      have hb : σ i x * w0 i x ^ T' ≠ 0 := mul_ne_zero hσi (pow_ne_zero _ hw)
      have e : f i x = (∑ k, s k i x / w0 i x * H k ⟨x, hxM⟩) * (σ i x * w0 i x ^ T') := by
        rw [← hid', div_mul_cancel₀ _ hb]
      simp only
      rw [e, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hG k, hpow]
      field_simp
    exact hEq.of_subset_closure (continuousOn_section_chart A hf i) hcont Set.inter_subset_left
      ((dense_Mset A hD hF).open_subset_closure_inter (A.chart i).open_source) hy

end

end ReciprocityTheory.L2DbarEstimates.Y
