import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianSumOfCounting
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaBound

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem countable_field : Countable F :=
  Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective

theorem card_places (h : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [← InfinitePlace.sum_mult_eq]
  have : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    simp [InfinitePlace.mult, h.isReal w]
  simp [this]

theorem posDef_lower {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → ℝ, c * ‖y‖ ^ 2 ≤ y ⬝ᵥ (P *ᵥ y) := by
  have hcont : Continuous fun y : ι → ℝ => y ⬝ᵥ (P *ᵥ y) := by fun_prop
  have hsph : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : ι → ℝ) 1, c ≤ u ⬝ᵥ (P *ᵥ u) := by
    rcases (Metric.sphere (0 : ι → ℝ) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
      refine ⟨u₀ ⬝ᵥ (P *ᵥ u₀), ?_, fun u hu => hmin hu⟩
      have hne0 : u₀ ≠ 0 := by
        rintro rfl
        simp at hu₀
      simpa using hP.dotProduct_mulVec_pos hne0
  obtain ⟨c, hc, hb⟩ := hsph
  refine ⟨c, hc, fun y => ?_⟩
  by_cases hy : y = 0
  · simp [hy]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hu : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hn]
  have := hb _ hu
  have e : (‖y‖⁻¹ • y) ⬝ᵥ (P *ᵥ (‖y‖⁻¹ • y)) = (‖y‖⁻¹) ^ 2 * (y ⬝ᵥ (P *ᵥ y)) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [e] at this
  have h2 : 0 < ‖y‖ ^ 2 := by positivity
  calc c * ‖y‖ ^ 2 ≤ (‖y‖⁻¹ ^ 2 * (y ⬝ᵥ (P *ᵥ y))) * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this h2.le
    _ = y ⬝ᵥ (P *ᵥ y) := by field_simp

theorem posDef_lower_family {W : Type} [Finite W] [Nonempty W] (P : W → Matrix ι ι ℝ)
    (hP : ∀ w, (P w).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ w, ∀ y : ι → ℝ, c * ‖y‖ ^ 2 ≤ y ⬝ᵥ (P w *ᵥ y) := by
  choose c hc hb using fun w => posDef_lower (hP w)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_min c
  refine ⟨c w₀, hc w₀, fun w y => le_trans ?_ (hb w y)⟩
  exact mul_le_mul_of_nonneg_right (hw₀ w) (by positivity)

theorem norm_gauss (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ) :
    ‖gauss B ρ P τ x‖ =
      Real.exp (-(Real.pi * ∑ w, (τ w).im * (x w ⬝ᵥ (P w *ᵥ x w)))) := by
  unfold gauss
  rw [Complex.norm_exp, Complex.re_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Complex.sub_re, Complex.mul_re, Complex.mul_im]
  ring

theorem sq_norm_le_sum {W : Type} [Fintype W] (x : W → ι → ℝ) :
    ‖x‖ ^ 2 ≤ ∑ w, ‖x w‖ ^ 2 := by
  have hs : 0 ≤ ∑ w, ‖x w‖ ^ 2 := Finset.sum_nonneg fun w _ => by positivity
  have : ‖x‖ ≤ Real.sqrt (∑ w, ‖x w‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun w => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun w => ‖x w‖ ^ 2) (fun w _ => by positivity) (Finset.mem_univ w)
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ w, ‖x w‖ ^ 2) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hs

theorem gauss_bound (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) {c t' : ℝ} (hc : 0 < c)
    (ht' : 0 < t') (hlow : ∀ w, ∀ y : ι → ℝ, c * ‖y‖ ^ 2 ≤ y ⬝ᵥ (P w *ᵥ y))
    (hτ : ∀ w, t' ≤ (τ w).im) (x : InfinitePlace F → ι → ℝ) :
    ‖gauss B ρ P τ x‖ ≤ Real.exp (-(Real.pi * c * t' * ‖x‖ ^ 2)) := by
  rw [norm_gauss, Real.exp_le_exp, neg_le_neg_iff]
  have h1 : t' * c * ∑ w, ‖x w‖ ^ 2 ≤ ∑ w, (τ w).im * (x w ⬝ᵥ (P w *ᵥ x w)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    calc t' * c * ‖x w‖ ^ 2 = t' * (c * ‖x w‖ ^ 2) := by ring
      _ ≤ (τ w).im * (x w ⬝ᵥ (P w *ᵥ x w)) :=
        mul_le_mul (hτ w) (hlow w _) (by positivity) (ht'.le.trans (hτ w))
  have h2 : t' * c * ‖x‖ ^ 2 ≤ t' * c * ∑ w, ‖x w‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (sq_norm_le_sum x) (by positivity)
  calc Real.pi * c * t' * ‖x‖ ^ 2 = Real.pi * (t' * c * ‖x‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h2.trans h1) Real.pi_pos.le

theorem wt_bound (M : ℕ) (τ : InfinitePlace F → ℂ) {T : ℝ} (h0 : ∀ w, 0 ≤ (τ w).im)
    (hT : ∀ w, (τ w).im ≤ T) :
    wt M τ ≤ Real.sqrt T ^ (Fintype.card (InfinitePlace F) * M) := by
  unfold wt
  calc ∏ w, Real.sqrt (τ w).im ^ M ≤ ∏ _w : InfinitePlace F, Real.sqrt T ^ M :=
        Finset.prod_le_prod (fun w _ => by positivity)
          (fun w _ => pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (hT w)) M)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm]

theorem phi_bound {φ : (ι → A F) → ℂ} (hφ : SB φ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ N : ℕ, 0 < N ∧
      (∀ y, ‖φ y‖ ≤ C₀) ∧ ∀ y, φ y ≠ 0 → ∀ i, (N : A F) * y i ∈ Oh F := by
  obtain ⟨hlc, hcs⟩ := hφ
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hlc.continuous
  have hK : IsCompact (⋃ i, (fun y : ι → A F => y i) '' tsupport φ) :=
    isCompact_iUnion fun i => hcs.isCompact.image (continuous_apply i)
  obtain ⟨N, hN, hb⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.2.1 _ hK
  refine ⟨max C 0, le_max_right _ _, N, hN, fun y => (hC y).trans (le_max_left _ _), fun y hy i => ?_⟩
  exact hb _ (Set.mem_iUnion.mpr ⟨i, y, subset_tsupport _ hy, rfl⟩)

theorem measurable_fin {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace (A F)] [BorelSpace (A F)]
    {gf : Ω → Matrix ι ι (A F)} (h : ∀ i j, Measurable fun ω => gf ω i j) (x : ι → F) :
    Measurable fun ω => gf ω *ᵥ fun j => algebraMap F (A F) (x j) := by
  haveI : SecondCountableTopology (A F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.1
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ => (h i j).mul_const _

theorem measurable_inf {Ω : Type} [MeasurableSpace Ω] {gi : Ω → InfinitePlace F → Matrix ι ι ℝ}
    (h : ∀ w i j, Measurable fun ω => gi ω w i j) (ρ : InfinitePlace F → (F →+* ℝ)) (x : ι → F) :
    Measurable fun ω => (fun w => gi ω w *ᵥ fun j => ρ w (x j) : InfinitePlace F → ι → ℝ) := by
  refine measurable_pi_iff.mpr fun w => measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ => (h w i j).mul_const _

theorem continuous_gauss (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    Continuous (gauss B ρ P τ) := by
  unfold gauss
  fun_prop

theorem measurable_term {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    {gf : Ω → Matrix ι ι (A F)} {gi : Ω → InfinitePlace F → Matrix ι ι ℝ}
    (hf : ∀ i j, Measurable fun ω => gf ω i j) (hi : ∀ w i j, Measurable fun ω => gi ω w i j)
    {φ : (ι → A F) → ℂ} (hφ : SB φ) (τ : InfinitePlace F → ℂ) (x : ι → F) :
    Measurable fun ω => thTerm B ρ P (gf ω) (gi ω) φ τ x := by
  haveI : SecondCountableTopology (A F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.1
  unfold thTerm
  exact (hφ.1.continuous.measurable.comp (measurable_fin hf x)).mul
    ((continuous_gauss B ρ P τ).measurable.comp (measurable_inf hi ρ x))

end GlobalTheory.CompanionTheory.SW.Core.ThetaBound

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaBound

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem term_le (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    {φ : (ι → A F) → ℂ} {C₀ : ℝ} {N : ℕ} (hC₀ : 0 ≤ C₀) (hb : ∀ y, ‖φ y‖ ≤ C₀)
    (hs : ∀ y, φ y ≠ 0 → ∀ i, (N : A F) * y i ∈ Oh F) (τ : InfinitePlace F → ℂ) {c t' : ℝ}
    (hc : 0 < c) (ht' : 0 < t') (hlow : ∀ w, ∀ y : ι → ℝ, c * ‖y‖ ^ 2 ≤ y ⬝ᵥ (P w *ᵥ y))
    (hτ : ∀ w, t' ≤ (τ w).im) (x : {x : ι → F // x ≠ 0}) :
    ‖thTerm B ρ P gf gi φ τ x.1‖ₑ ≤ ENNReal.ofReal C₀ *
      Set.indicator {x : {x : ι → F // x ≠ 0} |
        ∀ i, (N : A F) * (gf *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F}
        (fun x => ENNReal.ofReal (Real.exp (-(Real.pi * c * t' *
          ‖(fun w => gi w *ᵥ fun j => ρ w (x.1 j) : InfinitePlace F → ι → ℝ)‖ ^ 2)))) x := by
  by_cases hp : ∀ i, (N : A F) * (gf *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F
  · rw [Set.indicator_of_mem (by exact hp), ← ENNReal.ofReal_mul hC₀, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold thTerm
    rw [norm_mul]
    exact mul_le_mul (hb _) (gauss_bound B ρ P τ hc ht' hlow hτ _) (norm_nonneg _) hC₀
  · have h0 : φ (gf *ᵥ fun j => algebraMap F (A F) (x.1 j)) = 0 := by
      by_contra h
      exact hp (hs _ h)
    simp [thTerm, h0]

theorem add_le_mul_pow_of_sq_le_of_le_mul {w T κ C₀ C' : ℝ} {n : ℕ} (hT : 0 < T) (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hw0 : 0 ≤ w)
    (hw : w ≤ Real.sqrt (T / κ) ^ n) :
    w * (C₀ * (C' * (Real.sqrt T ^ n)⁻¹)) ≤ C₀ * |C'| * Real.sqrt κ⁻¹ ^ n := by
  have hs : Real.sqrt (T / κ) = Real.sqrt T * Real.sqrt κ⁻¹ := by
    rw [div_eq_mul_inv, Real.sqrt_mul hT.le]
  have hsT : 0 < Real.sqrt T ^ n := pow_pos (Real.sqrt_pos.mpr hT) n
  have h1 : w * (Real.sqrt T ^ n)⁻¹ ≤ Real.sqrt κ⁻¹ ^ n := by
    rw [← div_eq_mul_inv, div_le_iff₀ hsT, mul_comm (Real.sqrt κ⁻¹ ^ n), ← mul_pow, ← hs]
    exact hw
  have h2 : 0 ≤ w * (Real.sqrt T ^ n)⁻¹ := by positivity
  calc w * (C₀ * (C' * (Real.sqrt T ^ n)⁻¹)) = C₀ * C' * (w * (Real.sqrt T ^ n)⁻¹) := by ring
    _ ≤ C₀ * |C'| * (w * (Real.sqrt T ^ n)⁻¹) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hC₀) h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem theta_integral_bound : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ κ t : ℝ, 0 < κ → 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → (∀ v w, κ * (τ w).im ≤ (τ v).im) → (∀ x, Measurable fun ω => thTerm B ρ P (gf ω) (gi ω) φ τ x) ∧ ENNReal.ofReal (wt M τ) * ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr ≤ ENNReal.ofReal C := by
  intro F _ _ _ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hCD φ hφ κ t hκ ht
  obtain ⟨htr, -, -, -, -, hP, -⟩ := hQ
  obtain ⟨-, hgi, hgf, -, hcnt⟩ := hCD
  haveI : SecondCountableTopology (A F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.1
  haveI : Countable F := countable_field
  have hOh : MeasurableSet (Oh F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.1.measurableSet
  obtain ⟨C₀, hC₀, N, hN, hb, hs⟩ := phi_bound hφ
  obtain ⟨c, hc, hlow⟩ := posDef_lower_family P hP
  obtain ⟨Cc, hCc⟩ := hcnt N hN
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_sum_of_counting (Module.finrank ℚ F * M) (Real.pi * c) t Cc
    (mul_pos Real.pi_pos hc) ht
  have key := hC' {x : ι → F // x ≠ 0} Ω Pr
    (fun ω x => ‖(fun w => gi ω w *ᵥ fun j => ρ w (x.1 j) : InfinitePlace F → ι → ℝ)‖)
    (fun ω x => ∀ i, (N : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F)
    (fun x => continuous_norm.measurable.comp (measurable_inf hgi ρ x.1))
    (fun x => by
      have e : {ω | ∀ i, (N : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F} =
          ⋂ i, (fun ω => (N : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i) ⁻¹' Oh F := by
        ext ω
        simp
      rw [e]
      refine MeasurableSet.iInter fun i => ?_
      exact (((measurable_pi_apply i).comp (measurable_fin hgf x.1)).const_mul _) hOh)
    (fun ω x => norm_nonneg _)
    (fun R hR => by
      refine le_trans (le_of_eq ?_) ((hCc R hR).trans (le_of_eq ?_))
      · refine lintegral_congr fun ω => ?_
        unfold cnt
        refine tsum_congr fun x => ?_
        have hiff : (x ∈ {x : {x : ι → F // x ≠ 0} |
              (∀ i, (N : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F) ∧
              ‖(fun w => gi ω w *ᵥ fun j => ρ w (x.1 j) : InfinitePlace F → ι → ℝ)‖ ≤ R}) ↔
            (x.1 ∈ {x : ι → F |
              (∀ i v, ((N : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x j)) i) v ∈
                v.adicCompletionIntegers F) ∧
              ∀ w, ‖gi ω w *ᵥ fun j => ρ w (x j)‖ ≤ R}) := by
          simp only [Set.mem_setOf_eq]
          rw [pi_norm_le_iff_of_nonneg hR.le]
          rfl
        by_cases h : x.1 ∈ {x : ι → F |
              (∀ i v, ((N : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x j)) i) v ∈
                v.adicCompletionIntegers F) ∧
              ∀ w, ‖gi ω w *ᵥ fun j => ρ w (x j)‖ ≤ R}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.mp h'))]
      · congr 3
        ring_nf)
  refine ⟨C₀ * |C'| * Real.sqrt κ⁻¹ ^ (Module.finrank ℚ F * M), fun τ hτ hκτ => ?_⟩
  refine ⟨measurable_term B ρ P hgf hgi hφ τ, ?_⟩
  obtain ⟨v₀, hv₀⟩ := Finite.exists_min fun w => (τ w).im
  have ht' : t ≤ (τ v₀).im := hτ v₀
  have ht'pos : 0 < (τ v₀).im := ht.trans_le ht'
  have hk := key (τ v₀).im ht'
  have hterm : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal (C' * (Real.sqrt (τ v₀).im ^ (Module.finrank ℚ F * M))⁻¹) := by
    refine le_trans ?_ (mul_le_mul_right hk _)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun x => ?_
    refine (term_le B ρ P (gf ω) (gi ω) hC₀ hb hs τ hc ht'pos hlow hv₀ x).trans (le_of_eq ?_)
    congr 1
  have hw0 : 0 ≤ wt M τ := by
    unfold wt
    exact Finset.prod_nonneg fun w _ => by positivity
  have hwb : wt M τ ≤ Real.sqrt ((τ v₀).im / κ) ^ (Module.finrank ℚ F * M) := by
    rw [← card_places htr]
    refine wt_bound M τ (fun w => (ht.trans_le (hτ w)).le) fun w => ?_
    rw [le_div_iff₀' hκ]
    exact hκτ v₀ w
  calc ENNReal.ofReal (wt M τ) * ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0},
        ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr
      ≤ ENNReal.ofReal (wt M τ) * (ENNReal.ofReal C₀ *
          ENNReal.ofReal (C' * (Real.sqrt (τ v₀).im ^ (Module.finrank ℚ F * M))⁻¹)) :=
        mul_le_mul_right hterm _
    _ = ENNReal.ofReal (wt M τ * (C₀ *
          (C' * (Real.sqrt (τ v₀).im ^ (Module.finrank ℚ F * M))⁻¹))) := by
        rw [ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hC₀]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (add_le_mul_pow_of_sq_le_of_le_mul ht'pos hκ hC₀ hw0 hwb)

end GlobalTheory.CompanionTheory.SW.Core.ThetaBound
