import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepC

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}

theorem bsD_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (x : Y) (hx : x ∈ A.Mset w0 s De) :
    0 < A.nsq L w0 x ∧ 0 < A.nsq mu0 σ x ∧
      0 < ∑ k, ‖s k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      0 < ∑ k, ‖w k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      (jz A w0 s (A.pick x) x).det ≠ 0 := by
  obtain ⟨i0, hX0⟩ := hX
  refine ⟨bsA_nsq_pos A hx.1, bsA_nsq_pos A (hσ.2 x hx), ?_, ?_,
    jz_det_ne A hD hF x hx _ (A.mem_pick x)⟩
  · have h := bsB_z_ne A hx hX0
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i0))
    have : s i0 (A.pick x) x / w0 (A.pick x) x ≠ 0 := h
    positivity
  · obtain ⟨k, hk⟩ := hD.no_common_zero x
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ k))
    have : w k (A.pick x) x / w0 (A.pick x) x ≠ 0 := div_ne_zero hk hx.1
    positivity

theorem bsD_denom (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (m : ℕ) :
    A.IsSecOn (mu0 + m • L) (A.Mset w0 s De) (fun i y => σ i y * w0 i y ^ m) := by
  have hw := bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ (A.Mset w0 s De))
  refine ⟨fun i => ?_, ?_⟩
  · have h := (hσ.1.1 i).mul ((hw.1 i).pow m)
    refine h.congr fun v _ => ?_
    simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
  · intro i j y hy hi hj
    have h := bsA_tr_mul A hσ.1.2 (bsA_tr_pow A hw.2 m) i j y hy hi hj
    simpa only using h

theorem bsD_heq (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (f : ι → Y → ℂ) (x : A.Mset w0 s De) :
    ENNReal.ofReal (A.nsq (mu0 + T' • L) f x * A.sqn L s x ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w x ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick (x : Y)) x) /
      ‖(jz A w0 s (A.pick (x : Y)) x).det‖ ^ 2) =
    ENNReal.ofReal (‖f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')‖ ^ 2 *
      (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2 + 1)) *
      Real.exp (-bsPh0 A w w0 s mu0 σ x)) := by
  obtain ⟨ha, hnσ, hZ, hSw, hd⟩ := bsD_pos A hD hF hσ hX x x.2
  have hb : σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T' ≠ 0 :=
    mul_ne_zero (hσ.2 x x.2) (pow_ne_zero _ x.2.1)
  have e1 := bsC_nsq_prod A mu0 L T' f σ w0
    (f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')) x
    (div_mul_cancel₀ _ hb).symm
  have e2 := bsC_sqn_ratio A L s w0 x x.2.1
  have e3 := bsC_sqn_ratio A L w w0 x x.2.1
  have e4 := exp_neg_frameWeight_eq A w w0 s mu0 σ x hnσ hd hSw
  have hs0 : 0 ≤ A.sqn L s x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (s k) x
  have hw0 : 0 ≤ A.sqn L w x := Finset.sum_nonneg fun k _ => bsA_nsq_nonneg A L (w k) x
  have hp : 0 ≤ A.nsq (mu0 + T' • L) f x * A.sqn L s x ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w x ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (bsA_nsq_nonneg A _ f x) (Real.rpow_nonneg hs0 _))
      (Real.rpow_nonneg hw0 _)
  rw [← ENNReal.ofReal_mul hp]
  congr 1
  rw [e1, e2, e3, e4, show (T' : ℝ) - 3 / 2 + 1 = (T' : ℝ) - 1 / 2 by ring]
  exact bsC_alg _ _ _ _ _ _ T' ha hZ hSw

theorem bsD_hfin (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (T' : ℕ) (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∫⁻ x, ENNReal.ofReal
      (‖f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')‖ ^ 2 *
        (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2 + 1)) *
        Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤ := by
  have hφm : Measurable fun y => ENNReal.ofReal (A.nsq (mu0 + T' • L) f y *
      A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (((bsA_nsq_cont A hf).measurable.mul
      ((bsA_sqn_cont A hD.sec_s).measurable.pow_const _)).mul
      ((bsA_sqn_cont A hD.sec_w).measurable.pow_const _))
  have hflat := lintegral_flat A hD hF _ hφm
  have hc := lintegral_congr (μ := vol n (flatStein A hD hF).z) (bsD_heq A hD hF hσ hX T' f)
  rw [← hc, ← hflat]
  exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hint

theorem bsD_skoda (hS : SAll.{u} n) (hLSE : LSEAll.{u} n) (hn : 2 ≤ n) (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hpos : A.Pos (mu0 - A.kap) (fun _ => 0))
    (T' : ℕ) (hT : n + 1 ≤ T') (f : ι → Y → ℂ) (hf : A.IsSec (mu0 + T' • L) f)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T' • L) f y * A.sqn L s y ^ (-((T' : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∃ hh : Fin n → A.Mset w0 s De → ℂ, (∀ k, Holo n (flatStein A hD hF).z (hh k)) ∧
      (∀ x : A.Mset w0 s De, f (A.pick (x : Y)) x /
          (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T') =
        ∑ k, s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x * hh k x) ∧
      ∫⁻ x, ENNReal.ofReal ((∑ k, ‖hh k x‖ ^ 2) *
          (∑ k, ‖s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x‖ ^ 2) ^ (-((T' : ℝ) - 3 / 2)) *
          Real.exp (-bsPh0 A w w0 s mu0 σ x)) ∂vol n (flatStein A hD hF).z < ⊤ := by
  obtain ⟨hph0s, hph0l⟩ := smooth_leviNonneg_frameWeight A hD hF hLSE hσ hpos
  have hw0M := bsA_isSecOn_mono A hD.isSection_denom (Set.subset_univ (A.Mset w0 s De))
  have hg : ∀ k, Holo n (flatStein A hD hF).z
      (fun x : A.Mset w0 s De => s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x) := fun k =>
    bsB_holo_ratio A hD hF (a := s k) (b := w0) (bsA_isSecOn_mono A (hD.sec_s k) (Set.subset_univ _))
      hw0M fun y hy => hy.1
  have hnz : ∀ x : A.Mset w0 s De, ∃ k, s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x ≠ 0 := by
    intro x
    obtain ⟨i0, hX0⟩ := hX
    exact ⟨i0, bsB_z_ne A x.2 hX0⟩
  have ht : (n : ℝ) - 1 < (T' : ℝ) - 3 / 2 := by
    have : ((n + 1 : ℕ) : ℝ) ≤ T' := by exact_mod_cast hT
    push_cast at this; linarith
  have hFz : Holo n (flatStein A hD hF).z (fun x : A.Mset w0 s De =>
      f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T')) :=
    bsB_holo_ratio A hD hF (la := mu0 + T' • L) (a := f) (b := fun i y => σ i y * w0 i y ^ T')
      (bsA_isSecOn_mono A hf (Set.subset_univ _))
      (bsD_denom A hD hσ T') fun y hy => mul_ne_zero (hσ.2 y hy) (pow_ne_zero _ hy.1)
  have hfin := bsD_hfin A hD hF hσ hX T' f hf hint
  have hSk : SStatement n (A.Mset w0 s De) := hS (A.Mset w0 s De)
  obtain ⟨hh, h1, h2, h3⟩ := hSk (flatStein A hD hF) n
    (fun k (x : A.Mset w0 s De) => s k (A.pick (x : Y)) x / w0 (A.pick (x : Y)) x)
    (fun x => bsPh0 A w w0 s mu0 σ x) ((T' : ℝ) - 3 / 2)
    (fun x => f (A.pick (x : Y)) x / (σ (A.pick (x : Y)) x * w0 (A.pick (x : Y)) x ^ T'))
    hn hg hnz hph0s hph0l ht hFz hfin
  exact ⟨hh, h1, h2, lt_of_le_of_lt h3 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
