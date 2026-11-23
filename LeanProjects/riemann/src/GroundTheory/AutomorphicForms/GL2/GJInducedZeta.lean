import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJParabolicFubini
import GroundTheory.AutomorphicForms.GL2.GJLeviZeta
import GroundTheory.AutomorphicForms.HaarCosets
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Polynomial ValuativeRel Topology
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem mem_valBall_neg_iff {A : ℕ} {x : F} :
    x ∈ LocalField.valBall F (-(A : ℤ)) ↔ (uniformizer F : F) ^ A * x ∈ 𝒪[F] := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hϖA : (uniformizer F : F) ^ A ∈ LocalField.valBall F (A : ℤ) :=
    (mem_valBall_iff_exists (r := A)).2 ⟨1, one_mem _, by rw [mul_one]⟩
  constructor
  · intro hx
    have := LocalField.mul_mem_valBall hϖA hx
    rw [add_neg_cancel] at this
    exact LocalField.mem_valBall_zero_iff.1 this
  · intro h
    by_cases hx : x = 0
    · rw [hx]; exact zero_mem _
    have h0 := LocalField.mem_valBall_zero_iff.2 h
    have hne : (uniformizer F : F) ^ A * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hϖ) hx
    rw [LocalField.mem_valBall_iff_le_ord hne, LocalField.ord_mul (pow_ne_zero _ hϖ) hx,
      LocalField.ord_pow hϖ, LocalField.ord_uniformizer (irreducible_uniformizer F)] at h0
    rw [LocalField.mem_valBall_iff_le_ord hx]
    linarith

theorem ordDet_eq_zero_of_mem_integralGL {y : GL (Fin n) F} (hy : y ∈ integralGL F n) : ordDet y = 0 := by
  obtain ⟨u, rfl⟩ := hy
  have : ((integralGLHom F n u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      (((Matrix.GeneralLinearGroup.det u : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
    show ((RingHom.mapMatrix (𝒪[F]).subtype) (u : Matrix (Fin n) (Fin n) 𝒪[F])).det = _
    rw [← RingHom.map_det]
    rfl
  rw [ordDet, this]
  exact LocalField.ord_unit _

theorem detPow_mul_of_mem_integralGL (g : GL (Fin n) F) {y : GL (Fin n) F}
    (hy : y ∈ integralGL F n) (s : ℂ) : detPow (g * y) s = detPow g s := by
  have hg : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  have hy0 : (y : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det y).ne_zero
  have : ordDet (g * y) = ordDet g := by
    have h := ordDet_eq_zero_of_mem_integralGL hy
    rw [ordDet] at h ⊢
    rw [Units.val_mul, Matrix.det_mul, LocalField.ord_mul hg hy0, h, add_zero]
    rfl
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, this]

theorem continuous_detPow (s : ℂ) : Continuous fun g : GL (Fin n) F => detPow g s := by
  refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
  refine ⟨g • (integralGL F n : Set (GL (Fin n) F)), ?_, (isOpen_integralGL F n).smul g,
    ⟨1, one_mem _, mul_one g⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, detPow_mul_of_mem_integralGL g hk]
  exact hg

section Parabolic

variable {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem det_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
  rw [coe_parabolicMk, det_add_unipMatrix]

theorem detPow_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) (s : ℂ) :
    detPow ((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) s =
      detPow (m : GL (Fin n) F) s := by
  rw [detPow, detPow, absDet, absDet, det_parabolicMk]

end Parabolic

theorem IsSchwartzBruhat.comp_mulRight {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (y : GL (Fin n) F) :
    IsSchwartzBruhat fun X => Φ (X * (y : Matrix (Fin n) (Fin n) F)) := by
  let T : Matrix (Fin n) (Fin n) F ≃ₜ Matrix (Fin n) (Fin n) F :=
    { toFun := fun X => X * (y : Matrix (Fin n) (Fin n) F)
      invFun := fun X => X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      left_inv := fun X => by
        show X * (y : Matrix (Fin n) (Fin n) F) * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = X
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun X => by
        show X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) = X
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  exact ⟨hΦ.1.comp_continuous T.continuous, hΦ.2.comp_homeomorph T⟩

omit [Field F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in

theorem IsSchwartzBruhat.norm {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    IsSchwartzBruhat fun X => ((‖Φ X‖ : ℝ) : ℂ) :=
  ⟨hΦ.1.comp fun z => ((‖z‖ : ℝ) : ℂ),
    HasCompactSupport.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) hΦ.2 (by simp)⟩

theorem IsSchwartzBruhat.exists_mul_congruenceSubgroup {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ r : ℕ, ∀ X : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by
  obtain ⟨r₀, A, hinv, hsupp⟩ := hΦ.exists_invariant
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F

  have key : ∀ X : Matrix (Fin n) (Fin n) F, Φ X ≠ 0 → ∀ k ∈ congruenceSubgroup F n (r₀ + A),
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by
    intro X hX k hk
    obtain ⟨-, hk⟩ := (mem_congruenceSubgroup_iff F n).1 hk
    have ha : ∀ i j, ∃ a ∈ 𝒪[F], (k : Matrix (Fin n) (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j = (uniformizer F : F) ^ (r₀ + A) * a := by
      intro i j
      refine ⟨((k : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) /
        (uniformizer F : F) ^ (r₀ + A), ?_, by field_simp⟩
      rw [Valuation.mem_integer_iff, map_div₀, map_pow]
      exact div_le_one_of_le₀ (hk i j) zero_le
    choose a ha hka using ha
    have hXA := hsupp X hX
    have hY : ∀ i j, ∃ b ∈ 𝒪[F], (X * ((k : Matrix (Fin n) (Fin n) F) - 1)) i j =
        (uniformizer F : F) ^ r₀ * b := by
      intro i j
      refine ⟨∑ l, ((uniformizer F : F) ^ A * X i l) * a l j,
        Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hXA i l) (ha l j), ?_⟩
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.sub_apply, hka l j, pow_add]
      ring
    have := hinv X _ hY
    rwa [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel] at this
  refine ⟨r₀ + A, fun X k hk => ?_⟩
  by_cases hX : Φ X = 0
  · rw [hX]
    by_contra hne
    have h2 := key _ hne k⁻¹ (inv_mem hk)
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h2
    exact hne (h2.symm.trans hX)
  · exact key X hX k hk

section Unip

variable {α : Type*} [LinearOrder α] {β : Fin n → α} [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_unipMatrix :
    Continuous fun u : UnipotentIndex n β → F => unipMatrix F u := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : β i < β j
  · simp only [unipMatrix_apply_of_lt _ h]
    exact continuous_apply _
  · simp only [unipMatrix_apply_of_not_lt _ h]
    exact continuous_const

theorem integrable_add_unipMatrix (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔫.IsAddHaarMeasure]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    Integrable (fun u => Φ (X + unipMatrix F u)) μ𝔫 := by
  obtain ⟨r, A, -, hsupp⟩ := hΦ.exists_invariant
  refine Continuous.integrable_of_hasCompactSupport
    (hΦ.1.continuous.comp (continuous_const.add continuous_unipMatrix)) ?_
  refine HasCompactSupport.intro (K := Set.univ.pi fun _ => (LocalField.valBall F (-(A : ℤ)) : Set F))
    (isCompact_univ_pi fun _ => LocalField.isCompact_valBall _) fun u hu => ?_
  by_contra hne
  apply hu
  intro t _
  obtain ⟨⟨i, j⟩, h⟩ := t
  have h1 := hsupp _ hne i j
  rw [Matrix.add_apply, hX i j (ne_of_lt h), zero_add, unipMatrix_apply_of_lt _ h] at h1
  exact mem_valBall_neg_iff.2 h1

end Unip

section Cosets

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H]

theorem lintegral_eq_sum_coset (μ : Measure H) [μ.IsMulLeftInvariant] (L : Subgroup H)
    (hL : IsOpen (L : Set H)) [Fintype (H ⧸ L)] {u : H → ℝ≥0∞}
    (hu : ∀ h, ∀ l ∈ L, u (h * l) = u h) :
    ∫⁻ h, u h ∂μ = μ L * ∑ q : H ⧸ L, u q.out := by
  classical
  have hdec : ∀ h, u h = ∑ q : H ⧸ L, ((q.out • (L : Set H)).indicator fun _ => u q.out) h := by
    intro h
    rw [Finset.sum_eq_single (QuotientGroup.mk h : H ⧸ L)]
    · obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L h
      rw [Set.indicator_of_mem, hl, hu h l l.2]
      rw [hl]
      exact ⟨l⁻¹, inv_mem l.2, by simp [smul_eq_mul, mul_assoc]⟩
    · intro q _ hq
      rw [Set.indicator_of_notMem]
      rintro ⟨l, hl, rfl⟩
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq.2 (by simpa using hl)).symm
    · intro h'; exact absurd (Finset.mem_univ _) h'
  calc ∫⁻ h, u h ∂μ
      = ∫⁻ h, ∑ q : H ⧸ L, ((q.out • (L : Set H)).indicator fun _ => u q.out) h ∂μ :=
        lintegral_congr hdec
    _ = ∑ q : H ⧸ L, ∫⁻ h, ((q.out • (L : Set H)).indicator fun _ => u q.out) h ∂μ :=
        lintegral_finsetSum _ fun q _ => measurable_const.indicator (hL.smul _).measurableSet
    _ = ∑ q : H ⧸ L, u q.out * μ L := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lintegral_indicator_const (hL.smul _).measurableSet, measure_smul]
    _ = μ L * ∑ q : H ⧸ L, u q.out := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => mul_comm _ _

end Cosets

section Main

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem continuous_monoidHom_of_eq_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℝ≥0) (V : OpenSubgroup G) (hV : ∀ v ∈ V, χ v = 1) :
    Continuous χ := by
  refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg =>
    ⟨g • (V : Set G), ?_, V.isOpen.smul g, ⟨1, V.one_mem, mul_one g⟩⟩
  rintro _ ⟨v, hv, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, map_mul, hV v hv, mul_one]
  exact hg

variable (β) in

def leviSqrtModular : levi F n β →* ℝ≥0 where
  toFun m := NNReal.sqrt (Measure.modularCharacter (leviIncl m))
  map_one' := by simp
  map_mul' a b := by simp [NNReal.sqrt_mul]

theorem coe_leviSqrtModular (m : levi F n β) :
    ((leviSqrtModular β m : ℝ≥0) : ℂ) = sqrtModular F n β (leviIncl m) := rfl

theorem continuous_leviSqrtModular : Continuous (leviSqrtModular (F := F) β) := by
  refine continuous_monoidHom_of_eq_one _
    ⟨(integralGL F n).subgroupOf (levi F n β), isOpen_subgroupOf_levi (isOpen_integralGL F n)⟩ ?_
  intro v hv
  show NNReal.sqrt (Measure.modularCharacter (leviIncl v)) = 1
  rw [modularCharacter_eq_one_of_mem_integralGL (leviIncl v) (Subgroup.mem_subgroupOf.1 hv)]
  simp

def inducedIntegrand (Φ : Matrix (Fin n) (Fin n) F → ℂ) (φ : GL (Fin n) F → W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (g : GL (Fin n) F) : ℂ :=
  Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g)

omit [LinearOrder α] in
theorem continuous_inducedIntegrand {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    {φ : GL (Fin n) F → W} (hφ : ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
      ∀ k ∈ K, ∀ g, φ (g * k) = φ g) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    Continuous (inducedIntegrand Φ φ ℓ s) := by
  obtain ⟨K, hKo, hK⟩ := hφ
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K : Set (GL (Fin n) F)), ?_, hKo.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK k hk]
    exact hg
  exact ((hΦ.1.continuous.comp Units.continuous_val).mul (continuous_detPow s)).mul hℓφ

theorem inducedIntegrand_parabolicMk_mul {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    {y : GL (Fin n) F} (hy : y ∈ integralGL F n) (m : levi F n β)
    (u : UnipotentIndex n β → F) :
    inducedIntegrand Φ φ ℓ s (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) * y) =
      Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
          (y : Matrix (Fin n) (Fin n) F)) *
        (detPow (m : GL (Fin n) F) s * (sqrtModular F n β (leviIncl m) * ℓ (σ m (φ y)))) := by
  have h1 := hφ.1 (parabolicMk β m u) y
  rw [inflateTwist_apply, ← sqrtModular_leviProj, leviProj_parabolicMk] at h1
  rw [inducedIntegrand, Units.val_mul, coe_parabolicMk, detPow_mul_of_mem_integralGL _ hy,
    detPow_parabolicMk, h1, map_smul, smul_eq_mul]
  ring

theorem enorm_ofReal_complex {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

theorem enorm_coe_nnreal (x : ℝ≥0) : ‖((x : ℝ) : ℂ)‖ₑ = (x : ℝ≥0∞) := by
  rw [enorm_ofReal_complex (NNReal.coe_nonneg x), ENNReal.ofReal_coe_nnreal]

variable [MeasurableSpace F] [BorelSpace F]

theorem lintegral_inducedIntegrand_mul (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    {y : GL (Fin n) F} (hy : y ∈ integralGL F n) :
    ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y)‖ₑ
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫⁻ m, ‖leviIntegrand σ (leviRatio β * leviSqrtModular β)
          (fun X => ∫ u, ((‖Φ ((X + unipMatrix F u) * (y : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫)
          (φ y) ℓ s m‖ₑ ∂(haarLevi β μ𝔪) := by
  have hcont := continuous_inducedIntegrand hΦ hφ.2 ℓ s
  have hmeas : Measurable fun p : blockUpper F n β =>
      ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y)‖ₑ :=
    (hcont.comp (continuous_subtype_val.mul continuous_const)).enorm.measurable
  rw [lintegral_haarParabolic μ𝔪 μ𝔫 hmeas]
  refine lintegral_congr fun m => ?_
  have hΦy := hΦ.comp_mulRight y
  have hint := integrable_add_unipMatrix μ𝔫 hΦy (X := ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (mem_levi.1 m.2)
  have hmu : Measurable fun u : UnipotentIndex n β → F =>
      ‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
        (y : Matrix (Fin n) (Fin n) F))‖ₑ :=
    (hΦy.1.continuous.comp (continuous_const.add continuous_unipMatrix)).enorm.measurable
  simp_rw [inducedIntegrand_parabolicMk_mul hφ ℓ s hy m, enorm_mul]
  rw [lintegral_mul_const _ hmu, ← ofReal_integral_norm_eq_lintegral_enorm hint]
  have hI : 0 ≤ ∫ u, ‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
      (y : Matrix (Fin n) (Fin n) F))‖ ∂μ𝔫 := integral_nonneg fun _ => norm_nonneg _
  have hI' : (∫ u, ((‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
      (y : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫) =
      ((∫ u, ‖Φ ((((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) *
      (y : Matrix (Fin n) (Fin n) F))‖ ∂μ𝔫 : ℝ) : ℂ) := integral_complex_ofReal
  simp only [leviIntegrand, enorm_mul, MonoidHom.mul_apply]
  rw [hI', enorm_ofReal_complex hI, enorm_coe_nnreal, ← coe_leviSqrtModular, enorm_coe_nnreal,
    ENNReal.coe_mul]
  ring

theorem integral_inducedIntegrand_mul (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) (ℓ : Module.Dual ℂ W) (s : ℂ)
    {y : GL (Fin n) F} (hy : y ∈ integralGL F n)
    (hint : Integrable (fun p : blockUpper F n β => inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y))
      (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) :
    ∫ p, inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y)
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫ m, leviIntegrand σ (leviRatio β * leviSqrtModular β)
          (fun X => ∫ u, Φ ((X + unipMatrix F u) * (y : Matrix (Fin n) (Fin n) F)) ∂μ𝔫)
          (φ y) ℓ s m ∂(haarLevi β μ𝔪) := by
  rw [integral_haarParabolic μ𝔪 μ𝔫 hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only
  simp_rw [inducedIntegrand_parabolicMk_mul hφ ℓ s hy m]
  rw [integral_mul_const]
  simp only [leviIntegrand, MonoidHom.mul_apply, NNReal.coe_mul, Complex.ofReal_mul,
    coe_leviSqrtModular]
  ring

omit [MeasurableSpace F] [BorelSpace F] in

theorem lintegral_eq_sum_parabolic [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (integralGL F n)) [μK.IsHaarMeasure] {r : ℕ}
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))]
    {h : GL (Fin n) F → ℝ≥0∞} (hh : Measurable h)
    (hr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, h (g * k) = h g) :
    μG (integralGL F n) * (μK ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) *
      ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        ∫⁻ p, h ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP) =
      μP (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK Set.univ *
        ∫⁻ g, h g ∂μG := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have hLo : IsOpen (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) :=
    (isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val
  rw [← Measures.lintegral_mul_prod_eq (blockUpper F n β) (integralGL F n)
    (Measures.isClosed_blockUpper F n β) (isOpen_integralGL F n) (isCompact_integralGL F n)
    (fun g => exists_blockUpper_mul_integralGL' g) μG μP μK hh]
  congr 1
  have hinner : ∀ p : blockUpper F n β, ∫⁻ k, h ((p : GL (Fin n) F) * k) ∂μK =
      μK ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) * ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        h ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) := fun p =>
    lintegral_eq_sum_coset μK _ hLo (u := fun k => h ((p : GL (Fin n) F) * k)) fun k l hl => by
      show h ((p : GL (Fin n) F) * ((k * l : integralGL F n) : GL (Fin n) F)) =
        h ((p : GL (Fin n) F) * (k : GL (Fin n) F))
      rw [Subgroup.coe_mul, ← mul_assoc]
      exact hr _ _ (Subgroup.mem_subgroupOf.1 hl)
  simp_rw [hinner]
  have hmeas : ∀ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n), Measurable fun p : blockUpper F n β =>
      h ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) := fun q =>
    hh.comp (continuous_subtype_val.mul continuous_const).measurable
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun q _ => hmeas q),
    lintegral_finsetSum _ fun q _ => hmeas q]

omit [MeasurableSpace F] [BorelSpace F] in

theorem integral_eq_sum_parabolic [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (integralGL F n)) [μK.IsHaarMeasure] {r : ℕ}
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))]
    {f : GL (Fin n) F → ℂ} (hf : Integrable f μG)
    (hr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, f (g * k) = f g)
    (hint : ∀ y ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => f ((p : GL (Fin n) F) * y)) μP) :
    μG.real (integralGL F n) •
      (μK.real ((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Set (integralGL F n)) •
        ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
          ∫ p, f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP) =
      (μP.real (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ) •
        ∫ g, f g ∂μG := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hLo : IsOpen (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) :=
    (isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val
  have hLc : IsCompact (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) :=
    (Subgroup.isClosed_of_isOpen _ hLo).isCompact
  rw [← Measures.integral_mul_prod_eq (blockUpper F n β) (integralGL F n)
    (Measures.isClosed_blockUpper F n β) (isOpen_integralGL F n) (isCompact_integralGL F n)
    (fun g => exists_blockUpper_mul_integralGL' g) μG μP μK hf]
  congr 1
  have hinner : ∀ p : blockUpper F n β, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK =
      μK.real (((congruenceSubgroup F n r).subgroupOf (integralGL F n) : Subgroup (integralGL F n)) : Set (integralGL F n)) •
        ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) := by
    intro p
    have := integral_eq_smul_finsum_coset μK ⟨(congruenceSubgroup F n r).subgroupOf (integralGL F n), hLo⟩ hLc
      (f := fun k : integralGL F n => f ((p : GL (Fin n) F) * k))
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
      (fun k l hl => by
        show f ((p : GL (Fin n) F) * ((k * l : integralGL F n) : GL (Fin n) F)) =
          f ((p : GL (Fin n) F) * (k : GL (Fin n) F))
        rw [Subgroup.coe_mul, ← mul_assoc]
        exact hr _ _ (Subgroup.mem_subgroupOf.1 hl))
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  simp_rw [hinner]
  rw [integral_smul, integral_finsetSum _ fun q _ => hint _ (q.out).2]

theorem sum_eval_div_pow {ι : Type*} [Fintype ι] (N : ι → ℕ) (P : ι → ℂ[X]) (κ : ℂ) {x : ℂ}
    (hx : x ≠ 0) :
    κ * ∑ i, (P i).eval x / x ^ N i =
      (C κ * ∑ i, P i * X ^ (∑ j, N j - N i)).eval x / x ^ (∑ j, N j) := by
  classical
  rw [eval_mul, eval_C, eval_finsetSum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : N i ≤ ∑ j, N j := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  have hpow : x ^ (∑ j, N j) = x ^ (∑ j, N j - N i) * x ^ N i := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [eval_mul, eval_pow, eval_X, hpow]
  field_simp

end Main

variable {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem exists_inducedZeta (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ →
        ∀ φ ∈ parabolicIndSpace F n β σ, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
          (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
            Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g)) μG) ∧
          ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
            D.eval (qs F s) * ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g s * ℓ (φ g) ∂μG =
              P.eval (qs F s) / qs F s ^ N := by
  classical
  borelize F
  have : BorelSpace (levi F n β) := Subtype.borelSpace _
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  let μ𝔪 : Measure (LeviIndex n β → F) := Measure.addHaar
  let μ𝔫 : Measure (UnipotentIndex n β → F) := Measure.addHaar
  let μK : Measure (integralGL F n) := Measure.haar
  let θ : levi F n β →* ℝ≥0 := leviRatio β * leviSqrtModular β
  have hθ : Continuous θ := continuous_leviRatio.mul continuous_leviSqrtModular
  obtain ⟨s₀, D, hD0, hM⟩ := exists_leviZeta hσ hc θ hθ (haarLevi β μ𝔪)
  refine ⟨s₀, D, hD0, fun Φ hΦ φ hφ ℓ hℓ => ?_⟩

  obtain ⟨r₁, hr₁⟩ := hΦ.exists_mul_congruenceSubgroup
  obtain ⟨K', hK'o, hK'⟩ := hφ.2
  obtain ⟨r₂, -, hr₂⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)
  have hinv : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n (max r₁ r₂),
      inducedIntegrand Φ φ ℓ s (g * k) = inducedIntegrand Φ φ ℓ s g := by
    intro s g k hk
    have hk₀ : k ∈ integralGL F n := congruenceSubgroup_le F n _ hk
    simp only [inducedIntegrand, Units.val_mul]
    rw [hr₁ _ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk),
      detPow_mul_of_mem_integralGL g hk₀,
      hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g]
  have : Finite (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)) :=
    Subgroup.quotient_finite_of_isOpen _
      ((isOpen_congruenceSubgroup F n _).preimage continuous_subtype_val)
  let _ := Fintype.ofFinite
    (integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n))

  let Q := integralGL F n ⧸ (congruenceSubgroup F n (max r₁ r₂)).subgroupOf (integralGL F n)
  let y : Q → GL (Fin n) F := fun q => ((q.out : integralGL F n) : GL (Fin n) F)
  have hy : ∀ q, y q ∈ integralGL F n := fun q => (q.out).2
  let Ψ : Q → Matrix (Fin n) (Fin n) F → ℂ := fun q X =>
    ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F)) ∂μ𝔫
  let Ψa : Q → Matrix (Fin n) (Fin n) F → ℂ := fun q X =>
    ∫ u, ((‖Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))‖ : ℝ) : ℂ) ∂μ𝔫
  have hΨ : ∀ q, IsLeviSchwartz β (Ψ q) := fun q =>
    isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q))
  have hΨa : ∀ q, IsLeviSchwartz β (Ψa q) := fun q =>
    isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight (y q)).norm
  choose N Pq hNP using fun q => (hM (Ψ q) (hΨ q) (φ (y q)) ℓ hℓ).2
  have hcont : ∀ s, Continuous (inducedIntegrand Φ φ ℓ s) := fun s =>
    continuous_inducedIntegrand hΦ hφ.2 ℓ s

  have hintP : ∀ s : ℂ, s₀ < s.re → ∀ z ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z))
        (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) := by
    intro s hs z hz
    have hΨz := isLeviSchwartz_integral μ𝔫 (hΦ.comp_mulRight z).norm
    refine ⟨((hcont s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * z)‖ₑ
      ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) < ⊤
    rw [lintegral_inducedIntegrand_mul μ𝔪 μ𝔫 hΦ hφ ℓ s hz]
    exact ((hM _ hΨz (φ z) ℓ hℓ).1 s hs).2

  have hP0 : haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)
      (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0 :=
    ((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _
      ⟨1, by simp [one_mem]⟩
  have hK0 : μK Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μK Set.univ_nonempty

  have hintG : ∀ s : ℂ, s₀ < s.re → Integrable (inducedIntegrand Φ φ ℓ s) μG := by
    intro s hs
    refine ⟨(hcont s).aestronglyMeasurable, ?_⟩
    have hC := lintegral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))
      μK (hcont s).enorm.measurable (fun g k hk => by rw [hinv s g k hk])
    have hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf
        (integralGL F n)) * ∑ q : Q, ∫⁻ p, ‖inducedIntegrand Φ φ ℓ s
          ((p : GL (Fin n) F) * y q)‖ₑ ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) < ⊤ :=
      ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top
        (ENNReal.mul_lt_top (measure_lt_top _ _)
          (ENNReal.sum_lt_top.2 fun q _ => (hintP s hs (y q) (hy q)).2))
    rw [hC] at hlt
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)

  set κ : ℝ := (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)).real
      (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ with hκ
  set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n (max r₁ r₂)).subgroupOf
      (integralGL F n) : Set (integralGL F n)) with hκ'
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    have hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) :
        Set (blockUpper F n β)) :=
      (Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_integralGL F n)
    exact mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)
  have hformula : ∀ s : ℂ, s₀ < s.re → ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG =
      ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q : Q, ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪) := by
    intro s hs
    have hC := integral_eq_sum_parabolic (β := β) μG (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) μK
      (hintG s hs) (hinv s) (hintP s hs)
    have hB : ∀ q : Q, ∫ p, inducedIntegrand Φ φ ℓ s ((p : GL (Fin n) F) * y q)
        ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
        ∫ m, leviIntegrand σ θ (Ψ q) (φ (y q)) ℓ s m ∂(haarLevi β μ𝔪) := fun q =>
      integral_inducedIntegrand_mul μ𝔪 μ𝔫 hφ ℓ s (hy q) (hintP s hs _ (hy q))
    rw [Finset.sum_congr rfl fun q _ => hB q] at hC
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul] at hC
    have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ0
    rw [← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ'] at hC
    push_cast
    field_simp
    linear_combination hC.symm
  refine ⟨hintG, ∑ q, N q, C ((κ⁻¹ * κ' : ℝ) : ℂ) * ∑ q, Pq q * X ^ (∑ j, N j - N q),
    fun s hs => ?_⟩
  show D.eval (qs F s) * ∫ g, inducedIntegrand Φ φ ℓ s g ∂μG = _
  rw [hformula s hs, mul_left_comm, Finset.mul_sum,
    Finset.sum_congr rfl fun q _ => hNP q s hs]
  exact sum_eval_div_pow N Pq _ (qs_ne_zero s)

end GodementJacquet

end GroundTheory.Automorphic
