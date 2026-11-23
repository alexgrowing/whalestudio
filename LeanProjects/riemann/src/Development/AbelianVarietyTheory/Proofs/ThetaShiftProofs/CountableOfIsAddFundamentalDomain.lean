import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap

namespace GlobalTheory

open MeasureTheory Complex Module
open scoped Pointwise

noncomputable section

namespace TorusFourier

section Defs

variable {W W₁ : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W₁] [Module ℝ W₁]

def eNeg (χ : W →ₗ[ℝ] ℝ) (b : W) : ℂ := cexp (-(2 * Real.pi * I) * (χ b : ℂ))

def coeff [MeasurableSpace W] (μ : Measure W) (D : Set W) (f : W → ℂ) (χ : W →ₗ[ℝ] ℝ) : ℂ :=
  ⨍ b in D, f b * eNeg χ b ∂μ

def partialCoeff [MeasurableSpace W₁] (μ₁ : Measure W₁) (D₁ : Set W₁) (j : W₁ →ₗ[ℝ] W)
    (f : W → ℂ) (ν : W₁ →ₗ[ℝ] ℝ) (b : W) : ℂ :=
  coeff μ₁ D₁ (fun s => f (b + j s)) ν

def cubeCoeff {ι : Type*} [Fintype ι] (ω : ι → W) (f : W → ℂ) (χ : W →ₗ[ℝ] ℝ) : ℂ :=
  ∫ t in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1),
    f (∑ i, t i • ω i) * eNeg χ (∑ i, t i • ω i)

theorem eNeg_add (χ : W →ₗ[ℝ] ℝ) (a b : W) : eNeg χ (a + b) = eNeg χ a * eNeg χ b := by
  simp only [eNeg, map_add, ← Complex.exp_add]; congr 1; push_cast; ring

theorem eNeg_add_left (χ ψ : W →ₗ[ℝ] ℝ) (a : W) : eNeg (χ + ψ) a = eNeg χ a * eNeg ψ a := by
  simp only [eNeg, LinearMap.add_apply, ← Complex.exp_add]; congr 1; push_cast; ring

theorem eNeg_zero_left (a : W) : eNeg (0 : W →ₗ[ℝ] ℝ) a = 1 := by simp [eNeg]

theorem eNeg_comp (χ : W →ₗ[ℝ] ℝ) (j : W₁ →ₗ[ℝ] W) (s : W₁) :
    eNeg (χ ∘ₗ j) s = eNeg χ (j s) := rfl

theorem norm_eNeg (χ : W →ₗ[ℝ] ℝ) (a : W) : ‖eNeg χ a‖ = 1 := by
  have : -(2 * Real.pi * I) * (χ a : ℂ) = ((-(2 * Real.pi * χ a) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [eNeg, this, Complex.norm_exp_ofReal_mul_I]

theorem eNeg_eq_one_iff (χ : W →ₗ[ℝ] ℝ) (a : W) : eNeg χ a = 1 ↔ ∃ k : ℤ, χ a = k := by
  rw [eNeg, Complex.exp_eq_one_iff]
  have h : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have : (χ a : ℂ) = ((-n : ℤ) : ℝ) := by
      apply mul_left_cancel₀ h
      push_cast
      linear_combination -hn
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    exact ⟨-k, by rw [hk]; push_cast; ring⟩

theorem eNeg_neg_mul (χ : W →ₗ[ℝ] ℝ) (a : W) : eNeg (-χ) a * eNeg χ a = 1 := by
  rw [← eNeg_add_left, neg_add_cancel, eNeg_zero_left]

theorem exists_eNeg_ne_one {χ : W →ₗ[ℝ] ℝ} (h : χ ≠ 0) : ∃ a, eNeg χ a ≠ 1 := by
  obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (LinearMap.ext hc)
  refine ⟨(2 * χ a)⁻¹ • a, fun h1 => ?_⟩
  obtain ⟨k, hk⟩ := (eNeg_eq_one_iff _ _).1 h1
  have h2 : (2 * k : ℝ) = 1 := by
    rw [← hk, map_smul, smul_eq_mul]; field_simp
  have h3 : (2 * k : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem coeff_eq [MeasurableSpace W] (μ : Measure W) (D : Set W) (f : W → ℂ) (χ : W →ₗ[ℝ] ℝ) :
    coeff μ D f χ =
      ((μ.real D : ℂ))⁻¹ * ∫ b in D, f b * cexp (-(2 * Real.pi * I) * (χ b : ℂ)) ∂μ := by
  rw [coeff, setAverage_eq, Complex.real_smul]; push_cast; rfl

theorem periodic_span {ι : Type*} (ω : ι → W) {f : W → ℂ} (hf : ∀ i x, f (x + ω i) = f x) :
    ∀ l ∈ Submodule.span ℤ (Set.range ω), ∀ x, f (x + l) = f x := by
  intro l hl
  induction hl using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | zero => simp
  | add x y _ _ hx hy => intro z; rw [← add_assoc, hy, hx]
  | smul c x _ hx => exact Function.Periodic.zsmul (f := f) (c := x) hx c

theorem integral_span_iff {ι : Type*} (ω : ι → W) (χ : W →ₗ[ℝ] ℝ) :
    (∀ l ∈ Submodule.span ℤ (Set.range ω), ∃ k : ℤ, χ l = k) ↔ ∀ i, ∃ k : ℤ, χ (ω i) = k := by
  refine ⟨fun h i => h _ (Submodule.subset_span ⟨i, rfl⟩), fun h l hl => ?_⟩
  induction hl using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha]⟩

end Defs

section Domain

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] {μ : Measure W} [μ.IsAddHaarMeasure]

theorem continuous_eNeg (χ : W →ₗ[ℝ] ℝ) : Continuous (eNeg χ) := by
  have := χ.continuous_of_finiteDimensional
  unfold eNeg
  fun_prop

theorem countable_of_isAddFundamentalDomain {Γ : AddSubgroup W} {D : Set W}
    (hD : IsAddFundamentalDomain Γ D μ) (h0 : μ D ≠ 0) : Countable Γ := by
  have h := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ)
    (As := fun g : Γ => g +ᵥ D) (fun g => hD.nullMeasurableSet_vadd g) hD.aedisjoint
  have : {g : Γ | 0 < μ (g +ᵥ D)} = Set.univ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, measure_vadd]
    exact pos_iff_ne_zero.2 h0
  rw [this] at h
  exact Set.countable_univ_iff.1 h

theorem setIntegral_add_right {Γ : AddSubgroup W} [Countable Γ] {D : Set W}
    (hD : IsAddFundamentalDomain Γ D μ) {g : W → ℂ} (hg : ∀ l ∈ Γ, ∀ x, g (x + l) = g x)
    (a : W) : ∫ x in D, g (x + a) ∂μ = ∫ x in D, g x ∂μ := by
  have h1 := hD.setIntegral_eq (hD.vadd_of_comm a) (f := g) fun l x => by
    have := hg l l.2 x
    rw [add_comm] at this
    exact this
  rw [h1]
  have h2 := (measurePreserving_vadd a μ).setIntegral_image_emb
    (measurableEmbedding_const_vadd a) g D
  rw [show a +ᵥ D = (fun x => a +ᵥ x) '' D from rfl, h2]
  simp only [vadd_eq_add, add_comm]

theorem coeff_congr_domain {Γ : AddSubgroup W} [Countable Γ] {D D' : Set W}
    (hD : IsAddFundamentalDomain Γ D μ) (hD' : IsAddFundamentalDomain Γ D' μ) {f : W → ℂ}
    (hf : ∀ l ∈ Γ, ∀ x, f (x + l) = f x) {χ : W →ₗ[ℝ] ℝ} (hχ : ∀ l ∈ Γ, ∃ k : ℤ, χ l = k) :
    coeff μ D f χ = coeff μ D' f χ := by
  simp only [coeff, setAverage_eq, Measure.real, hD.measure_eq hD']
  congr 1
  refine hD.setIntegral_eq hD' fun l x => ?_
  have : l +ᵥ x = x + l := add_comm _ _
  rw [this, hf l l.2, eNeg_add, (eNeg_eq_one_iff _ _).2 (hχ l l.2), mul_one]

theorem coeff_translate {Γ : AddSubgroup W} [Countable Γ] {D : Set W}
    (hD : IsAddFundamentalDomain Γ D μ) {f : W → ℂ}
    (hf : ∀ l ∈ Γ, ∀ x, f (x + l) = f x) {χ : W →ₗ[ℝ] ℝ} (hχ : ∀ l ∈ Γ, ∃ k : ℤ, χ l = k)
    (a : W) : coeff μ D (fun x => f (x + a)) χ = eNeg (-χ) a * coeff μ D f χ := by
  simp only [coeff, setAverage_eq]
  rw [mul_smul_comm, ← setIntegral_add_right hD (g := fun b => f b * eNeg χ b) ?_ a,
    ← integral_const_mul]
  · congr 2
    ext x
    rw [eNeg_add]
    linear_combination (-(f (x + a) * eNeg χ x)) * eNeg_neg_mul χ a
  · intro l hl x
    rw [hf l hl, eNeg_add, (eNeg_eq_one_iff _ _).2 (hχ l hl), mul_one]

theorem coeff_eq_zero_of_period {Γ : AddSubgroup W} [Countable Γ] {D : Set W}
    (hD : IsAddFundamentalDomain Γ D μ) {f : W → ℂ}
    (hf : ∀ l ∈ Γ, ∀ x, f (x + l) = f x) {χ : W →ₗ[ℝ] ℝ} (hχ : ∀ l ∈ Γ, ∃ k : ℤ, χ l = k)
    {a : W} (ha : ∀ x, f (x + a) = f x) (hχa : ¬ ∃ k : ℤ, χ a = k) : coeff μ D f χ = 0 := by
  have h := coeff_translate hD hf hχ a
  simp only [ha] at h
  have h1 : eNeg χ a ≠ 1 := fun h => hχa ((eNeg_eq_one_iff _ _).1 h)
  have h2 : (eNeg χ a - 1) * coeff μ D f χ = 0 := by
    have h3 := eNeg_neg_mul χ a
    change coeff μ D f χ = _ at h
    linear_combination (eNeg χ a) * h + (coeff μ D f χ) * h3
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)

theorem coeff_one_of_ne_zero {Γ : AddSubgroup W} [Countable Γ] {D : Set W}
    (hD : IsAddFundamentalDomain Γ D μ) {χ : W →ₗ[ℝ] ℝ} (hχ : ∀ l ∈ Γ, ∃ k : ℤ, χ l = k)
    (h0 : χ ≠ 0) : coeff μ D (fun _ => 1) χ = 0 := by
  obtain ⟨a, ha⟩ := exists_eNeg_ne_one h0
  exact coeff_eq_zero_of_period hD (fun _ _ _ => rfl) hχ (a := a) (fun _ => rfl)
    fun h => ha ((eNeg_eq_one_iff _ _).2 h)

theorem coeff_one_zero {D : Set W} (h0 : μ D ≠ 0) (h1 : μ D ≠ ⊤) :
    coeff μ D (fun _ => 1) 0 = 1 := by
  simp only [coeff, eNeg_zero_left, mul_one]
  exact setAverage_const h0 h1 1

end Domain

section Lattice

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] {μ : Measure W} [μ.IsAddHaarMeasure]

omit [MeasurableSpace W] [BorelSpace W] in
theorem countable_toAddSubgroup (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] :
    Countable L.toAddSubgroup := inferInstanceAs (Countable L)

omit [MeasurableSpace W] [BorelSpace W] in

theorem exists_basis (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ (n : ℕ) (ω : Basis (Fin n) ℝ W), Submodule.span ℤ (Set.range ω) = L :=
  ⟨_, (Module.finBasis ℤ L).ofZLatticeBasis ℝ L, Basis.ofZLatticeBasis_span ℝ L _⟩

omit [MeasurableSpace W] [BorelSpace W] in

theorem exists_bound (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] {f : W → ℂ}
    (hc : Continuous f) (hf : ∀ l ∈ L, ∀ x, f (x + l) = f x) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨n, ω, rfl⟩ := exists_basis L
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded ω).isCompact_closure.exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  have h := hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain ω x))
  rw [← hf _ (ZSpan.floor ω x).2, ZSpan.fract, sub_add_cancel] at h
  exact h

theorem measure_ne_zero_ne_top (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L]
    {D : Set W} (hD : IsAddFundamentalDomain L D μ) : μ D ≠ 0 ∧ μ D ≠ ⊤ := by
  obtain ⟨n, ω, rfl⟩ := exists_basis L
  haveI := countable_toAddSubgroup (Submodule.span ℤ (Set.range ω))
  have h : μ D = μ (ZSpan.fundamentalDomain ω) :=
    IsAddFundamentalDomain.measure_eq (G := (Submodule.span ℤ (Set.range ω)).toAddSubgroup) hD
      (ZSpan.isAddFundamentalDomain' ω μ)
  rw [h]
  exact ⟨ZSpan.measure_fundamentalDomain_ne_zero ω,
    (ZSpan.fundamentalDomain_isBounded ω).measure_lt_top.ne⟩

theorem coeff_eq_cubeCoeff {ι : Type*} [Fintype ι] (ω : Basis ι ℝ W) {D : Set W}
    (hD : IsAddFundamentalDomain (Submodule.span ℤ (Set.range ω)) D μ) {f : W → ℂ}
    (hf : ∀ l ∈ Submodule.span ℤ (Set.range ω), ∀ x, f (x + l) = f x) {χ : W →ₗ[ℝ] ℝ}
    (hχ : ∀ l ∈ Submodule.span ℤ (Set.range ω), ∃ k : ℤ, χ l = k) :
    coeff μ D f χ = cubeCoeff ω f χ := by
  haveI := countable_toAddSubgroup (Submodule.span ℤ (Set.range ω))
  rw [coeff_congr_domain (Γ := (Submodule.span ℤ (Set.range ω)).toAddSubgroup) hD
    (ZSpan.isAddFundamentalDomain' ω μ) hf hχ]
  set φ : (ι → ℝ) ≃L[ℝ] W := ω.equivFunL.symm with hφ
  have hφa : ∀ t, φ t = ∑ i, t i • ω i := fun t => ω.equivFun_symm_apply t
  set μ' : Measure W := (volume : Measure (ι → ℝ)).map φ with hμ'
  haveI : μ'.IsAddHaarMeasure := φ.isAddHaarMeasure_map _
  have hpre : φ ⁻¹' ZSpan.fundamentalDomain ω = Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 1 := by
    ext t
    have : ∀ i, ω.repr (φ t) i = t i := fun i =>
      congrFun (ω.equivFun.apply_symm_apply t) i
    simp [ZSpan.mem_fundamentalDomain, this]
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  have h1 : μ' (ZSpan.fundamentalDomain ω) = 1 := by
    rw [hμ', hemb.map_apply, hpre, Real.volume_pi_Ico]; simp
  have h2 : ∀ g : W → ℂ, ∫ x in ZSpan.fundamentalDomain ω, g x ∂μ' =
      ∫ t in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1), g (φ t) := fun g => by
    rw [hμ', hemb.setIntegral_map, hpre]
    exact setIntegral_congr_set (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ => volume))
  have h3 : μ = Measure.addHaarScalarFactor μ μ' • μ' := Measure.isAddLeftInvariant_eq_smul μ μ'
  have h4 : Measure.addHaarScalarFactor μ μ' ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ μ').ne'
  generalize Measure.addHaarScalarFactor μ μ' = c at h3 h4
  rw [coeff, setAverage_eq, h3, Measure.restrict_smul, integral_smul_nnreal_measure, h2,
    Measure.real, Measure.smul_apply, h1, cubeCoeff]
  simp only [hφa]
  rw [NNReal.smul_def, smul_smul]
  simp [h4]

theorem eq_zero_iff (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] {D : Set W}
    (hD : IsAddFundamentalDomain L D μ) {f : W → ℂ} (hc : Continuous f)
    (hf : ∀ l ∈ L, ∀ x, f (x + l) = f x) :
    f = 0 ↔ ∀ χ : W →ₗ[ℝ] ℝ, (∀ l ∈ L, ∃ k : ℤ, χ l = k) → coeff μ D f χ = 0 := by
  refine ⟨fun h χ _ => by simp [h, coeff], fun h => ?_⟩
  obtain ⟨n, ω, rfl⟩ := exists_basis L
  have key := ReciprocityTheory.ChartRestriction.G.I2.tof_torus_unique (fun t : Fin n → ℝ => f (∑ i, t i • ω i))
    (hc.comp (by fun_prop)) (fun x m => by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      refine hf _ (Submodule.sum_mem _ fun i _ => ?_) _
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) (fun m => by
      set χ : W →ₗ[ℝ] ℝ := ∑ i, (m i : ℝ) • ω.coord i with hχd
      have hχω : ∀ i, χ (ω i) = m i := fun i => by
        simp [hχd, Finsupp.single_apply]
      have hχ := (integral_span_iff ω χ).2 fun i => ⟨_, hχω i⟩
      have h1 := h χ hχ
      rw [coeff_eq_cubeCoeff ω hD hf hχ, cubeCoeff] at h1
      rw [← h1]
      have : {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
          Set.univ.pi fun _ => Set.Ioc 0 1 := by ext; simp
      rw [this]
      refine (setIntegral_congr_set (Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ => volume))).trans ?_
      congr 1
      ext t
      rw [mul_comm, eNeg]
      congr 2
      simp only [map_sum, map_smul, hχω, smul_eq_mul]
      push_cast
      simp only [mul_comm (m _ : ℂ), neg_mul])
  ext x
  have := key (ω.repr x)
  simpa using this

end Lattice

section Partial

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] {μ : Measure W} [μ.IsAddHaarMeasure]
  {W₁ : Type*} [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [MeasurableSpace W₁] [BorelSpace W₁] {μ₁ : Measure W₁} [μ₁.IsAddHaarMeasure]

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] [μ₁.IsAddHaarMeasure] in

theorem continuous_partialCoeff {D₁ : Set W₁} (h1 : μ₁ D₁ ≠ ⊤) (j : W₁ →ₗ[ℝ] W) {f : W → ℂ}
    (hc : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (ν : W₁ →ₗ[ℝ] ℝ) :
    Continuous (partialCoeff μ₁ D₁ j f ν) := by
  have hj := j.continuous_of_finiteDimensional
  have hν := continuous_eNeg ν
  haveI : IsFiniteMeasure (μ₁.restrict D₁) := isFiniteMeasure_restrict.2 h1
  unfold partialCoeff coeff
  simp only [setAverage_eq]
  refine Continuous.const_smul ?_ _
  refine continuous_of_dominated (bound := fun _ => C) (fun b => ?_) (fun b => ?_)
    (integrable_const C) ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_eNeg, mul_one]; exact hC _
  · exact Filter.Eventually.of_forall fun s => by fun_prop

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] [μ₁.IsAddHaarMeasure]
  [FiniteDimensional ℝ W₁] [BorelSpace W₁] in

theorem partialCoeff_add_period (D₁ : Set W₁) (j : W₁ →ₗ[ℝ] W) {f : W → ℂ} (ν : W₁ →ₗ[ℝ] ℝ)
    {l : W} (hl : ∀ x, f (x + l) = f x) (b : W) :
    partialCoeff μ₁ D₁ j f ν (b + l) = partialCoeff μ₁ D₁ j f ν b := by
  unfold partialCoeff
  congr 1
  ext s
  rw [add_right_comm, hl]

theorem coeff_partialCoeff_eq_mul (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L]
    {D : Set W} (hD : IsAddFundamentalDomain L D μ) {D₁ : Set W₁} (h1 : μ₁ D₁ ≠ ⊤)
    (j : W₁ →ₗ[ℝ] W) {f : W → ℂ} (hc : Continuous f) (hf : ∀ l ∈ L, ∀ x, f (x + l) = f x)
    (ν : W₁ →ₗ[ℝ] ℝ) {χ : W →ₗ[ℝ] ℝ} (hχ : ∀ l ∈ L, ∃ k : ℤ, χ l = k) :
    coeff μ D (partialCoeff μ₁ D₁ j f ν) χ =
      coeff μ₁ D₁ (fun _ => 1) (ν - χ ∘ₗ j) * coeff μ D f χ := by
  haveI := countable_toAddSubgroup L
  obtain ⟨C, hC⟩ := exists_bound L hc hf
  have hj := j.continuous_of_finiteDimensional
  have hν := continuous_eNeg ν
  have hχc := continuous_eNeg χ
  haveI : IsFiniteMeasure (μ₁.restrict D₁) := isFiniteMeasure_restrict.2 h1
  haveI : IsFiniteMeasure (μ.restrict D) :=
    isFiniteMeasure_restrict.2 (measure_ne_zero_ne_top L hD).2
  have hint : Integrable (Function.uncurry fun (b : W) (s : W₁) =>
      f (b + j s) * eNeg ν s * eNeg χ b) ((μ.restrict D).prod (μ₁.restrict D₁)) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) C
      (Filter.Eventually.of_forall fun p => ?_)
    · unfold Function.uncurry; fun_prop
    · simp only [Function.uncurry, norm_mul, norm_eNeg, mul_one]; exact hC _
  have hs : ∀ s, (μ.real D)⁻¹ • ∫ b in D, f (b + j s) * eNeg ν s * eNeg χ b ∂μ =
      eNeg (ν - χ ∘ₗ j) s * coeff μ D f χ := fun s => by
    have := coeff_translate (Γ := L.toAddSubgroup) hD hf hχ (j s)
    rw [sub_eq_add_neg, eNeg_add_left, mul_assoc, ← LinearMap.neg_comp, eNeg_comp, ← this, coeff,
      setAverage_eq, mul_smul_comm, ← integral_const_mul]
    congr 2
    ext b
    ring
  calc coeff μ D (partialCoeff μ₁ D₁ j f ν) χ
      = (μ.real D)⁻¹ • ∫ b in D, (μ₁.real D₁)⁻¹ •
          ∫ s in D₁, f (b + j s) * eNeg ν s * eNeg χ b ∂μ₁ ∂μ := by
        simp only [partialCoeff, coeff, setAverage_eq, integral_mul_const, smul_mul_assoc]
    _ = (μ₁.real D₁)⁻¹ • ∫ s in D₁, (μ.real D)⁻¹ •
          ∫ b in D, f (b + j s) * eNeg ν s * eNeg χ b ∂μ ∂μ₁ := by
        rw [integral_smul, integral_smul, integral_integral_swap hint, smul_comm]
    _ = _ := by
        simp only [hs, integral_mul_const]
        simp only [coeff, setAverage_eq, one_mul, smul_mul_assoc]

open Classical in

theorem coeff_partialCoeff (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L]
    {D : Set W} (hD : IsAddFundamentalDomain L D μ) {L₁ : AddSubgroup W₁} {D₁ : Set W₁}
    (hD₁ : IsAddFundamentalDomain L₁ D₁ μ₁) (h0 : μ₁ D₁ ≠ 0) (h1 : μ₁ D₁ ≠ ⊤)
    (j : W₁ →ₗ[ℝ] W) {f : W → ℂ} (hc : Continuous f) (hf : ∀ l ∈ L, ∀ x, f (x + l) = f x)
    (hf₁ : ∀ l ∈ L₁, ∀ x, f (x + j l) = f x)
    {ν : W₁ →ₗ[ℝ] ℝ} (hν : ∀ l ∈ L₁, ∃ k : ℤ, ν l = k)
    {χ : W →ₗ[ℝ] ℝ} (hχ : ∀ l ∈ L, ∃ k : ℤ, χ l = k) :
    coeff μ D (partialCoeff μ₁ D₁ j f ν) χ = if χ ∘ₗ j = ν then coeff μ D f χ else 0 := by
  haveI := countable_toAddSubgroup L
  haveI := countable_of_isAddFundamentalDomain hD₁ h0
  rw [coeff_partialCoeff_eq_mul L hD h1 j hc hf ν hχ]
  split_ifs with h
  · rw [h, sub_self, coeff_one_zero h0 h1, one_mul]
  · by_cases hi : ∀ l ∈ L₁, ∃ k : ℤ, χ (j l) = k
    · rw [coeff_one_of_ne_zero hD₁ ?_ (sub_ne_zero.2 (Ne.symm h)), zero_mul]
      intro l hl
      obtain ⟨a, ha⟩ := hν l hl
      obtain ⟨b, hb⟩ := hi l hl
      exact ⟨a - b, by simp [ha, hb]⟩
    · push Not at hi
      obtain ⟨l, hl, hk⟩ := hi
      rw [coeff_eq_zero_of_period (Γ := L.toAddSubgroup) hD hf hχ (hf₁ l hl)
        (fun ⟨k, h⟩ => hk k h), mul_zero]

theorem partialCoeff_eq_zero_iff (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L]
    {D : Set W} (hD : IsAddFundamentalDomain L D μ) {L₁ : AddSubgroup W₁} {D₁ : Set W₁}
    (hD₁ : IsAddFundamentalDomain L₁ D₁ μ₁) (h0 : μ₁ D₁ ≠ 0) (h1 : μ₁ D₁ ≠ ⊤)
    (j : W₁ →ₗ[ℝ] W) {f : W → ℂ} (hc : Continuous f) (hf : ∀ l ∈ L, ∀ x, f (x + l) = f x)
    (hf₁ : ∀ l ∈ L₁, ∀ x, f (x + j l) = f x)
    {ν : W₁ →ₗ[ℝ] ℝ} (hν : ∀ l ∈ L₁, ∃ k : ℤ, ν l = k) :
    partialCoeff μ₁ D₁ j f ν = 0 ↔
      ∀ χ : W →ₗ[ℝ] ℝ, (∀ l ∈ L, ∃ k : ℤ, χ l = k) → χ ∘ₗ j = ν → coeff μ D f χ = 0 := by
  obtain ⟨C, hC⟩ := exists_bound L hc hf
  rw [eq_zero_iff L hD (continuous_partialCoeff h1 j hc hC ν)
    fun l hl x => partialCoeff_add_period D₁ j ν (hf l hl) x]
  refine forall_congr' fun χ => forall_congr' fun hχ => ?_
  rw [coeff_partialCoeff L hD hD₁ h0 h1 j hc hf hf₁ hν hχ]
  by_cases h : χ ∘ₗ j = ν <;> simp [h]

open Classical in

theorem partialCoeff_spec_map (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L]
    {D : Set W} (hD : IsAddFundamentalDomain L D μ) {L₁ : AddSubgroup W₁} {D₁ : Set W₁}
    (hD₁ : IsAddFundamentalDomain L₁ D₁ μ₁) (h0 : μ₁ D₁ ≠ 0) (h1 : μ₁ D₁ ≠ ⊤)
    (j : W₁ →ₗ[ℝ] W) {f : W → ℂ} (hc : Continuous f) (hf : ∀ l ∈ L, ∀ x, f (x + l) = f x)
    (hf₁ : ∀ l ∈ L₁, ∀ x, f (x + j l) = f x) :
    (∀ ν : W₁ →ₗ[ℝ] ℝ, (∀ l ∈ L₁, ∃ k : ℤ, ν l = k) →
      Continuous (partialCoeff μ₁ D₁ j f ν) ∧
      (∀ l ∈ L, ∀ b, partialCoeff μ₁ D₁ j f ν (b + l) = partialCoeff μ₁ D₁ j f ν b) ∧
      (∀ χ : W →ₗ[ℝ] ℝ, (∀ l ∈ L, ∃ k : ℤ, χ l = k) →
        coeff μ D (partialCoeff μ₁ D₁ j f ν) χ = if χ ∘ₗ j = ν then coeff μ D f χ else 0) ∧
      (partialCoeff μ₁ D₁ j f ν = 0 ↔
        ∀ χ : W →ₗ[ℝ] ℝ, (∀ l ∈ L, ∃ k : ℤ, χ l = k) → χ ∘ₗ j = ν → coeff μ D f χ = 0)) ∧
    (∀ χ : W →ₗ[ℝ] ℝ, (∀ l ∈ L, ∃ k : ℤ, χ l = k) → (¬ ∀ l ∈ L₁, ∃ k : ℤ, χ (j l) = k) →
      coeff μ D f χ = 0) ∧
    (f = 0 ↔ ∀ χ : W →ₗ[ℝ] ℝ, (∀ l ∈ L, ∃ k : ℤ, χ l = k) → coeff μ D f χ = 0) := by
  haveI := countable_toAddSubgroup L
  obtain ⟨C, hC⟩ := exists_bound L hc hf
  refine ⟨fun ν hν => ⟨continuous_partialCoeff h1 j hc hC ν,
    fun l hl b => partialCoeff_add_period D₁ j ν (hf l hl) b,
    fun χ hχ => coeff_partialCoeff L hD hD₁ h0 h1 j hc hf hf₁ hν hχ,
    partialCoeff_eq_zero_iff L hD hD₁ h0 h1 j hc hf hf₁ hν⟩, fun χ hχ hi => ?_,
    eq_zero_iff L hD hc hf⟩
  push Not at hi
  obtain ⟨l, hl, hk⟩ := hi
  exact coeff_eq_zero_of_period (Γ := L.toAddSubgroup) hD hf hχ (hf₁ l hl) fun ⟨k, h⟩ => hk k h

omit [MeasurableSpace W] [BorelSpace W] in
open Classical in

theorem partialCoeff_spec_cube {ι : Type*} [Fintype ι] (ω : Basis ι ℝ W)
    {L₁ : AddSubgroup W₁} {D₁ : Set W₁}
    (hD₁ : IsAddFundamentalDomain L₁ D₁ μ₁) (h0 : μ₁ D₁ ≠ 0) (h1 : μ₁ D₁ ≠ ⊤)
    (j : W₁ →ₗ[ℝ] W) {f : W → ℂ} (hc : Continuous f) (hf : ∀ i x, f (x + ω i) = f x)
    (hf₁ : ∀ l ∈ L₁, ∀ x, f (x + j l) = f x) :
    (∀ ν : W₁ →ₗ[ℝ] ℝ, (∀ l ∈ L₁, ∃ k : ℤ, ν l = k) →
      Continuous (partialCoeff μ₁ D₁ j f ν) ∧
      (∀ i b, partialCoeff μ₁ D₁ j f ν (b + ω i) = partialCoeff μ₁ D₁ j f ν b) ∧
      (∀ χ : W →ₗ[ℝ] ℝ, (∀ i, ∃ k : ℤ, χ (ω i) = k) →
        cubeCoeff ω (partialCoeff μ₁ D₁ j f ν) χ = if χ ∘ₗ j = ν then cubeCoeff ω f χ else 0) ∧
      (partialCoeff μ₁ D₁ j f ν = 0 ↔
        ∀ χ : W →ₗ[ℝ] ℝ, (∀ i, ∃ k : ℤ, χ (ω i) = k) → χ ∘ₗ j = ν → cubeCoeff ω f χ = 0)) ∧
    (∀ χ : W →ₗ[ℝ] ℝ, (∀ i, ∃ k : ℤ, χ (ω i) = k) → (¬ ∀ l ∈ L₁, ∃ k : ℤ, χ (j l) = k) →
      cubeCoeff ω f χ = 0) ∧
    (f = 0 ↔ ∀ χ : W →ₗ[ℝ] ℝ, (∀ i, ∃ k : ℤ, χ (ω i) = k) → cubeCoeff ω f χ = 0) := by
  borelize W
  have hD := ZSpan.isAddFundamentalDomain ω (Measure.addHaar : Measure W)
  have hf' := periodic_span ω hf
  obtain ⟨H₁, H₂, H₃⟩ := partialCoeff_spec_map _ hD hD₁ h0 h1 j hc hf' hf₁
  have e : ∀ χ : W →ₗ[ℝ] ℝ, (∀ i, ∃ k : ℤ, χ (ω i) = k) →
      coeff Measure.addHaar (ZSpan.fundamentalDomain ω) f χ = cubeCoeff ω f χ := fun χ hχ =>
    coeff_eq_cubeCoeff ω hD hf' ((integral_span_iff ω χ).2 hχ)
  simp only [integral_span_iff] at H₁ H₂ H₃
  refine ⟨fun ν hν => ?_, fun χ hχ hi => e χ hχ ▸ H₂ χ hχ hi, ?_⟩
  · obtain ⟨a, b, c, d⟩ := H₁ ν hν
    refine ⟨a, fun i => b _ (Submodule.subset_span ⟨i, rfl⟩), fun χ hχ => ?_, ?_⟩
    · rw [← e χ hχ, ← c χ hχ, coeff_eq_cubeCoeff ω hD b ((integral_span_iff ω χ).2 hχ)]
    · rw [d]
      exact forall_congr' fun χ => forall_congr' fun hχ => by rw [e χ hχ]
  · rw [H₃]
    exact forall_congr' fun χ => forall_congr' fun hχ => by rw [e χ hχ]

end Partial

end TorusFourier

end

end GlobalTheory
