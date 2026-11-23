import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem finFd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (fd μ) := by
  have h := (isFiniteMeasure_quotientMeasure (K := K) (n := n) μ).measure_univ_lt_top
  rw [quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain _ μ)] at h
  exact ⟨by rwa [Measure.restrict_apply_univ]⟩

private theorem intg {Z E : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [NormedAddCommGroup E] [SecondCountableTopology E]
    (ν : Measure Z) [IsFiniteMeasure ν] {h : Z → E} (hc : Continuous h) {C : ℝ} (hb : ∀ z, ‖h z‖ ≤ C) :
    Integrable h ν :=
  Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hb)

private theorem contInt {Y Z E : Type} [TopologicalSpace Y] [FirstCountableTopology Y] [TopologicalSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    (ν : Measure Z) [IsFiniteMeasure ν] {h : Y × Z → E} (hc : Continuous h) {C : ℝ} (hb : ∀ z, ‖h z‖ ≤ C) :
    Continuous (fun y => ∫ z, h (y, z) ∂ν) ∧ ∀ y, ‖∫ z, h (y, z) ∂ν‖ ≤ C * ν.real univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => C) (fun y => ?_) (fun y => ae_of_all _ fun z => hb _)
    (integrable_const C) (ae_of_all _ fun z => hc.comp (by fun_prop)), fun y => ?_⟩
  · exact (hc.comp (Continuous.prodMk_right y)).aestronglyMeasurable
  · exact norm_integral_le_of_norm_le_const (ae_of_all _ fun z => hb _)

private theorem orth {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} {v w : L2 μ}
    {φ ψ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w ψ) :
    ∫ m, conj (φ m) * ψ m ∂fd μ = ⟪v, w⟫_ℂ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_of_ae hw] with y h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

private theorem posFd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {φ : G1 K n → ℝ} (hc : Continuous φ) {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C) (h0 : ∀ z, 0 ≤ φ z)
    (hΓ : ∀ (γ : Gam K n) z, φ (γ * z) = φ z) {z₀ : G1 K n} (hz : φ z₀ ≠ 0) : 0 < ∫ z, φ z ∂fd μ := by
  haveI := finFd μ
  rw [integral_pos_iff_support_of_nonneg h0 (intg _ hc hb), pos_iff_ne_zero]
  intro h
  rw [Measure.restrict_apply hc.isOpen_support.measurableSet] at h
  have := (isFundamentalDomain_fundamentalDomain (Gam K n) μ).measure_zero_of_invariant _ (by
    intro γ
    ext z
    rw [mem_smul_set_iff_inv_smul_mem]
    show φ ((γ⁻¹ : Gam K n) * z) ≠ 0 ↔ φ z ≠ 0
    rw [hΓ]) h
  exact (hc.isOpen_support.measure_pos μ ⟨z₀, hz⟩).ne' this

private theorem bdd2 {K : Type} [Field K] [NumberField K] {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') :
    ∃ C : ℝ, ∀ x y, ‖conj (f x) * f' y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨C', hC'⟩ := hf'.bdd
  refine ⟨C * C', fun x y => ?_⟩
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (hC x) (hC' y) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

private theorem core0 {M G : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [TopologicalSpace G] [FirstCountableTopology G] [Mul G] [ContinuousMul G] (ν : Measure M) [IsFiniteMeasure ν]
    {f f' : G → ℂ} (h1 : Continuous f) (h2 : Continuous f') {C : ℝ} (hC : ∀ x y, ‖conj (f x) * f' y‖ ≤ C)
    {a b : M × M → G} (ha : Continuous a) (hb : Continuous b) :
    (∀ x y, Integrable (fun m => conj (f (a m * x)) * f' (b m * y)) (ν.prod ν)) ∧
    Continuous (fun p : G × G => ∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * p.1)) * f' (b (m₁, m₂) * p.2) ∂ν ∂ν) ∧
    ∃ C : ℝ, ∀ x y, ‖∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * x)) * f' (b (m₁, m₂) * y) ∂ν ∂ν‖ ≤ C := by
  have hi : ∀ x y, Integrable (fun m => conj (f (a m * x)) * f' (b m * y)) (ν.prod ν) :=
    fun x y => intg _ (by fun_prop) fun _ => hC _ _
  have := contInt (ν.prod ν) (h := fun q : (G × G) × M × M =>
    conj (f (a q.2 * q.1.1)) * f' (b q.2 * q.1.2)) (by fun_prop) fun _ => hC _ _
  simp only [integral_prod _ (hi _ _)] at this
  exact ⟨hi, this.1, _, fun x y => this.2 (x, y)⟩

private theorem core {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') {a b : G1 K 2 × G1 K 2 → G1 K (2 + 2)}
    (ha : Continuous a) (hb : Continuous b) :
    (∀ x y, Integrable (fun m => conj (f (a m * x)) * f' (b m * y)) ((fd μ₂).prod (fd μ₂))) ∧
    Continuous (fun p : G1 K (2 + 2) × G1 K (2 + 2) =>
      ∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * p.1)) * f' (b (m₁, m₂) * p.2) ∂fd μ₂ ∂fd μ₂) ∧
    ∃ C : ℝ, ∀ x y, ‖∫ m₁, ∫ m₂, conj (f (a (m₁, m₂) * x)) * f' (b (m₁, m₂) * y) ∂fd μ₂ ∂fd μ₂‖ ≤ C := by
  haveI := finFd μ₂
  obtain ⟨C, hC⟩ := bdd2 hf hf'
  exact core0 (fd μ₂) hf.cont hf'.cont hC ha hb

private theorem lin0 {M : Type} [MeasurableSpace M] (ν : Measure M) [IsFiniteMeasure ν] (a : ℂ) {u v w : M × M → ℂ}
    (i1 : Integrable (fun m => u m * v m) (ν.prod ν)) (i2 : Integrable (fun m => u m * w m) (ν.prod ν)) :
    ∫ x, ∫ y, u (x, y) * (a * v (x, y) + w (x, y)) ∂ν ∂ν =
      a * ∫ x, ∫ y, u (x, y) * v (x, y) ∂ν ∂ν + ∫ x, ∫ y, u (x, y) * w (x, y) ∂ν ∂ν := by
  have e3 := integral_prod _ ((i1.const_mul a).add i2)
  have e4 := integral_add (i1.const_mul a) i2
  rw [integral_const_mul, integral_prod _ i1, integral_prod _ i2] at e4
  refine Eq.trans ?_ (e3.symm.trans e4)
  simp only [Pi.add_apply, mul_add, mul_left_comm]

private theorem zero0 {M : Type} [MeasurableSpace M] (ν : Measure M) [IsFiniteMeasure ν] {u : M × M → ℂ}
    (i1 : Integrable u (ν.prod ν)) (h : ∀ y, ∫ x, u (x, y) ∂ν = 0) : ∫ x, ∫ y, u (x, y) ∂ν ∂ν = 0 := by
  rw [← integral_prod _ i1, integral_prod_symm _ i1]
  simp only [h, integral_zero]

private theorem contLv {K : Type} [Field K] [NumberField K] : Continuous fun m : G1 K 2 × G1 K 2 => lv m.1 m.2 0 :=
  (blkLaws (K := K)).2.2.2.1.comp (f := fun m : G1 K 2 × G1 K 2 => (m.1, m.2, (0 : ℝ)))
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

private theorem pos2 {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {F : G1 K n × G1 K n → ℂ} (hc : Continuous F) {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C)
    (hΓ : ∀ (γ₁ γ₂ : Gam K n) (a b : G1 K n), F ((γ₁ : G1 K n) * a, (γ₂ : G1 K n) * b) = F (a, b))
    {m₁ m₂ : G1 K n} (hz : F (m₁, m₂) ≠ 0) : 0 < ∫ a, ∫ b, ‖F (a, b)‖ ^ 2 ∂fd μ ∂fd μ := by
  haveI := finFd μ
  have hc2 : Continuous fun m => ‖F m‖ ^ 2 := hc.norm.pow 2
  have hb2 : ∀ m, ‖‖F m‖ ^ 2‖ ≤ C ^ 2 := fun m => by
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
  have hin := contInt (fd μ) hc2 hb2
  refine posFd μ hin.1 hin.2 (fun z => integral_nonneg fun _ => sq_nonneg _) (fun γ z => ?_) (z₀ := m₁) (ne_of_gt ?_)
  · refine integral_congr_ae (ae_of_all _ fun b => ?_)
    have := hΓ γ 1 z b
    rw [OneMemClass.coe_one, one_mul] at this
    exact congrArg (fun c : ℂ => ‖c‖ ^ 2) this
  · refine posFd μ (φ := fun b => ‖F (m₁, b)‖ ^ 2) (hc2.comp (Continuous.prodMk_right m₁)) (fun b => hb2 (m₁, b))
      (fun _ => sq_nonneg _) (fun γ b => ?_) (z₀ := m₂) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
    have := hΓ 1 γ m₁ b
    rw [OneMemClass.coe_one, one_mul] at this
    exact congrArg (fun c : ℂ => ‖c‖ ^ 2) this

private theorem posPt {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (hne : f ≠ 0) :
    ∃ k ∈ KG K (2 + 2), 0 < ∫ m₁, ∫ m₂, ‖f (lv m₁ m₂ 0 * k)‖ ^ 2 ∂fd μ₂ ∂fd μ₂ := by
  haveI := finFd μ₂
  have hmul := (blkLaws (K := K)).2.1
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
  obtain ⟨X, m₁, m₂, t, k, hkK, rfl⟩ := iwa g
  refine ⟨k, hkK, ?_⟩
  have hg' : f (lv m₁ m₂ 0 * k) ≠ 0 := by
    rw [← hf.ray t, ← mul_assoc, hmul, one_mul, one_mul, add_zero, ← hf.unip X, ← mul_assoc]
    exact hg
  have hΓ : ∀ (γ₁ γ₂ : Gam K 2) (a b : G1 K 2),
      f (lv ((γ₁ : G1 K 2) * a) ((γ₂ : G1 K 2) * b) 0 * k) = f (lv a b 0 * k) := fun γ₁ γ₂ a b => by
    have hm : nn (0 : unipLattice K (2 + 2) 2).1 * lv (γ₁ : G1 K 2) γ₂ 0 ∈ PK K :=
      ((pkLaws (K := K)).2.1 _).mpr ⟨0, γ₁, γ₂, rfl⟩
    rw [← hf.rat _ hm (lv a b 0 * k), mul_assoc, hf.unip, ← mul_assoc, hmul, add_zero]
  obtain ⟨C, hC⟩ := hf.bdd
  exact pos2 μ₂ (F := fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * k)) (hf.cont.comp (contLv.mul continuous_const))
    (fun _ => hC _) hΓ hg'

private theorem contK {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') : Continuous fun k : KG K (2 + 2) => pm μ₂ f f' k k :=
  (core μ₂ hf hf' contLv contLv).2.1.comp
    (f := fun k : KG K (2 + 2) => ((k : G1 K (2 + 2)), (k : G1 K (2 + 2))))
    (continuous_subtype_val.prodMk continuous_subtype_val)

private theorem cptK {K : Type} [Field K] [NumberField K] : CompactSpace (KG K (2 + 2)) :=
  isCompact_iff_compactSpace.mp ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1

private theorem intK {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure]
    {f f' : G1 K (2 + 2) → ℂ} (hf : SFun f) (hf' : SFun f') : Integrable (fun k : KG K (2 + 2) => pm μ₂ f f' k k) κ :=
  haveI := cptK (K := K)
  (contK μ₂ hf hf').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem posK {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure]
    {f : G1 K (2 + 2) → ℂ} (hf : SFun f) (hne : f ≠ 0) : 0 < (∫ k : KG K (2 + 2), pm μ₂ f f k k ∂κ).re := by
  haveI := cptK (K := K)
  obtain ⟨k, hkK, hpos⟩ := posPt μ₂ hf hne
  have hre : ∀ x, (pm μ₂ f f x x).re = ∫ m₁, ∫ m₂, ‖f (lv m₁ m₂ 0 * x)‖ ^ 2 ∂fd μ₂ ∂fd μ₂ := fun x => by
    rw [← Complex.ofReal_re (∫ m₁, ∫ m₂, ‖f (lv m₁ m₂ 0 * x)‖ ^ 2 ∂fd μ₂ ∂fd μ₂)]
    simp only [pm, ← integral_complex_ofReal, Complex.conj_mul', Complex.ofReal_pow]
  rw [← RCLike.re_to_complex, ← integral_re (intK μ₂ κ hf hf)]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (f := fun k : KG K (2 + 2) => (pm μ₂ f f k k).re)
    (Complex.continuous_re.comp (contK μ₂ hf hf))
    (HasCompactSupport.of_compactSpace _) (fun x => ?_) (x := ⟨k, hkK⟩) (ne_of_gt ?_)
  · exact (integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _).trans_eq (hre x).symm
  · exact hpos.trans_eq (hre k).symm

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pmLaws :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure], (∀ (τ₁ τ₂ ρ₁ ρ₂ : Submodule ℂ (L2 μ₂)) (f f' : G1 K (2 + 2) → ℂ), SFun f → SFun f' → Slices τ₁ τ₂ f → Slices ρ₁ ρ₂ f' → ∀ x y,
        (τ₁ ⟂ ρ₁ → pm μ₂ f f' x y = 0) ∧ (τ₁ ⟂ ρ₂ → pw μ₂ f f' x y = 0)) ∧
      (∀ f f' f'' : G1 K (2 + 2) → ℂ, SFun f → SFun f' → SFun f'' → ∀ a : ℂ,
        ∫ k : KG K (2 + 2), pm μ₂ f (a • f' + f'') k k ∂κ = a * ∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ + ∫ k : KG K (2 + 2), pm μ₂ f f'' k k ∂κ ∧
        conj (∫ k : KG K (2 + 2), pm μ₂ f f' k k ∂κ) = ∫ k : KG K (2 + 2), pm μ₂ f' f k k ∂κ) ∧
      (∀ f : G1 K (2 + 2) → ℂ, SFun f → f ≠ 0 → 0 < (∫ k : KG K (2 + 2), pm μ₂ f f k k ∂κ).re) ∧
      ∀ f f' : G1 K (2 + 2) → ℂ, SFun f → SFun f' → Continuous (fun p : G1 K (2 + 2) × G1 K (2 + 2) => pw μ₂ f f' p.1 p.2) ∧ ∃ C : ℝ, ∀ x y, ‖pw μ₂ f f' x y‖ ≤ C := by
  intro K _ _ μ₂ _ κ _
  haveI := finFd μ₂
  have ha := contLv (K := K)
  have hb : Continuous fun m : G1 K 2 × G1 K 2 => lv m.2 m.1 0 :=
    (blkLaws (K := K)).2.2.2.1.comp (f := fun m : G1 K 2 × G1 K 2 => (m.2, m.1, (0 : ℝ)))
      (continuous_snd.prodMk (continuous_fst.prodMk continuous_const))
  refine ⟨fun τ₁ τ₂ ρ₁ ρ₂ f f' hf hf' hs hs' x y => ⟨fun ho => ?_, fun ho => ?_⟩,
    fun f f' f'' hf hf' hf'' a => ⟨?_, ?_⟩, fun f hf hne => posK μ₂ κ hf hne, fun f f' hf hf' => (core μ₂ hf hf' ha hb).2⟩
  · refine zero0 (fd μ₂) ((core μ₂ hf hf' ha ha).1 x y) fun m₂ => ?_
    obtain ⟨v, hv, hr⟩ := (hs x).1 m₂
    obtain ⟨w, hw, hr'⟩ := (hs' y).1 m₂
    exact (orth hr hr').trans (ho.inner_eq hv hw)
  · refine zero0 (fd μ₂) ((core μ₂ hf hf' ha hb).1 x y) fun m₂ => ?_
    obtain ⟨v, hv, hr⟩ := (hs x).1 m₂
    obtain ⟨w, hw, hr'⟩ := (hs' y).2 m₂
    exact (orth hr hr').trans (ho.inner_eq hv hw)
  · rw [← integral_const_mul, ← integral_add ((intK μ₂ κ hf hf').const_mul a) (intK μ₂ κ hf hf'')]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    exact lin0 (fd μ₂) a ((core μ₂ hf hf' ha ha).1 k k) ((core μ₂ hf hf'' ha ha).1 k k)
  · rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only [pm, ← integral_conj, map_mul, RCLike.conj_conj, mul_comm]
