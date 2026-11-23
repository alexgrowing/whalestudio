import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.IsHilbertSchmidtOfAeEqDual
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem det_unipMatrix {r : ℕ} {R : Type*} [CommRing R] (X : UPos n r → R) :
    (unipMatrix X).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have h : ¬ ((i : ℕ) < r ∧ r ≤ (i : ℕ)) := by omega
    simp [unipMatrix, blockEntry_apply, h]
  · intro i j hij
    have hji : (j : ℕ) < i := hij
    have h1 : i ≠ j := fun h => by rw [h] at hji; exact lt_irrefl _ hji
    have h2 : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) := by omega
    simp [unipMatrix, blockEntry_apply, h1, h2]

theorem unipGL_mem_normOneGL {r : ℕ} (X : UPos n r → 𝔸[K]) :
    unipGL X ∈ normOneGL K n := by
  have h1 : AdelicGLn.det K n (unipGL X) = 1 :=
    Units.ext (by rw [AdelicGLn.coe_det, coe_unipGL, det_unipMatrix, Units.val_one])
  rw [mem_normOneGL, h1, map_one]
  rfl

variable (K n) in

def unipOne (r : ℕ) (X : UPos n r → 𝔸[K]) : normOneGL K n :=
  ⟨unipGL X, unipGL_mem_normOneGL X⟩

@[simp] theorem coe_unipOne (r : ℕ) (X : UPos n r → 𝔸[K]) :
    (unipOne K n r X : AdelicGLn.AdelicGL K n) = unipGL X := rfl

theorem unipOne_add (r : ℕ) (X Y : UPos n r → 𝔸[K]) :
    unipOne K n r (X + Y) = unipOne K n r X * unipOne K n r Y :=
  Subtype.ext (unipGL_add X Y)

theorem unipOne_zero (r : ℕ) : unipOne K n r 0 = 1 :=
  Subtype.ext unipGL_zero

theorem continuous_unipOne (r : ℕ) : Continuous (unipOne K n r) :=
  continuous_induced_rng.2 continuous_unipGL

theorem unipOne_mem_rationalGLOne (r : ℕ) (ξ : unipLattice K n r) :
    unipOne K n r ξ ∈ rationalGLOne K n := by
  obtain ⟨_, ξ, rfl⟩ := ξ
  change unipGL (fun p => algebraMap K 𝔸[K] (ξ p)) ∈ AdelicGLn.rationalGL K n
  rw [← diagonal_unipGL]
  exact ⟨unipGL ξ, rfl⟩

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

instance (r : ℕ) : SigmaFinite (unipMeasure K n r) := by
  unfold unipMeasure
  infer_instance

theorem lintegral_lift_le {T : Set (normOneGL K n)}
    (hT : IsCompact T) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      (∫⁻ y in T, ‖ψ (mk Γ₁ y)‖ₑ ∂μ) ^ 2 ≤ C * ‖ψ‖ₑ ^ 2 := by
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ₁ hT
  refine ⟨μ T * N, ENNReal.mul_ne_top hT.measure_lt_top.ne (by simp), fun ψ => ?_⟩
  have h := L2Kernel.lintegral_mul_sq_le (μ.restrict T) (f := fun _ => 1)
    (g := fun y => ‖ψ (mk Γ₁ y)‖ₑ) aemeasurable_const
    (stronglyMeasurable_lift Γ₁ μ ψ).measurable.enorm.aemeasurable
  simp only [one_mul, one_pow, lintegral_const, Measure.restrict_apply_univ] at h
  refine h.trans ?_
  rw [mul_assoc]
  gcongr
  exact lintegral_lift_sq_le Γ₁ μ ψ hT.measurableSet hN

theorem ae_of_forall_isCompact {p : normOneGL K n → Prop}
    (h : ∀ S : Set (normOneGL K n), IsCompact S → ∀ᵐ y ∂μ.restrict S, p y) : ∀ᵐ y ∂μ, p y := by
  have : ∀ᵐ y ∂μ.restrict (⋃ k, compactCovering (normOneGL K n) k), p y :=
    (ae_restrict_iUnion_iff _ _).2 fun k => h _ (isCompact_compactCovering _ k)
  rwa [iUnion_compactCovering, Measure.restrict_univ] at this

theorem continuous_unipOne_mul (r : ℕ) :
    Continuous fun p : (UPos n r → 𝔸[K]) × normOneGL K n => unipOne K n r p.1 * p.2 :=
  ((continuous_unipOne r).comp continuous_fst).mul continuous_snd

theorem setLIntegral_mul_left (F : normOneGL K n → ℝ≥0∞) (g : normOneGL K n)
    {S : Set (normOneGL K n)} (hS : IsCompact S) :
    ∫⁻ y in S, F (g * y) ∂μ = ∫⁻ z in (g * ·) '' S, F z ∂μ := by
  have hS' : MeasurableSet ((g * ·) '' S) := (hS.image (continuous_const_mul g)).measurableSet
  rw [← lintegral_indicator hS.measurableSet, ← lintegral_indicator hS']
  refine Eq.trans ?_ (lintegral_mul_left_eq_self (fun z => ((g * ·) '' S).indicator F z) g)
  congr 1
  ext y
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (mem_image_of_mem _ hy)]
  · rw [indicator_of_notMem hy, indicator_of_notMem]
    rintro ⟨y', hy', h⟩
    exact hy (mul_left_cancel h ▸ hy')

theorem exists_lintegral_unip_sq_le (r : ℕ) {S : Set (normOneGL K n)} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      (∫⁻ y in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r ∂μ) ^ 2 ≤ C * ‖φ‖ₑ ^ 2 := by
  obtain ⟨D', hD'c, hDD'⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n)
    (r := r)
  set T := (fun p : (UPos n r → 𝔸[K]) × normOneGL K n => unipOne K n r p.1 * p.2) '' (D' ×ˢ S)
  have hT : IsCompact T := (hD'c.prod hS).image (continuous_unipOne_mul r)
  obtain ⟨C, hC, hCφ⟩ := lintegral_lift_le μ hT
  refine ⟨C, hC, fun φ => le_trans (pow_le_pow_left₀ zero_le ?_ 2) (hCφ φ)⟩
  have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
      ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
    ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
      (continuous_unipOne_mul r).measurable)).enorm
  have hswap : ∫⁻ y in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r ∂μ =
      ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ y in S,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂μ ∂unipMeasure K n r := by
    refine lintegral_lintegral_swap ?_
    exact (hmeas.comp measurable_swap).aemeasurable
  rw [hswap]
  calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ y in S,
        ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂μ ∂unipMeasure K n r
      ≤ ∫⁻ _ in unipFundamentalDomain K n r, ∫⁻ y in T, ‖φ (mk Γ₁ y)‖ₑ ∂μ ∂unipMeasure K n r := by
        refine setLIntegral_mono' measurableSet_unipFundamentalDomain fun X hX => ?_
        rw [setLIntegral_mul_left μ (fun z => ‖φ (mk Γ₁ z)‖ₑ) (unipOne K n r X) hS]
        refine lintegral_mono_set ?_
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨(X, y), ⟨hDD' hX, hy⟩, rfl⟩
    _ = ∫⁻ y in T, ‖φ (mk Γ₁ y)‖ₑ ∂μ := by
        rw [setLIntegral_const, unipMeasure_unipFundamentalDomain, mul_one]

variable (K n) in

def ctFun (r : ℕ) (F : RightCosetSpace Γ₁ → ℂ) (y : normOneGL K n) : ℂ :=
  ∫ X in unipFundamentalDomain K n r, F (mk Γ₁ (unipOne K n r X * y)) ∂unipMeasure K n r

def constantTermL2 (r : ℕ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (y : normOneGL K n) : ℂ :=
  ctFun K n r φ y

theorem ae_ae_unip_notMem {Z : Set (RightCosetSpace Γ₁)} (hZ : quotientMeasure Γ₁ μ Z = 0)
    (r : ℕ) : ∀ᵐ y ∂μ, ∀ᵐ X ∂unipMeasure K n r, mk Γ₁ (unipOne K n r X * y) ∉ Z := by
  set Z' := toMeasurable (quotientMeasure Γ₁ μ) Z
  have hZ' : quotientMeasure Γ₁ μ Z' = 0 := by rw [measure_toMeasurable]; exact hZ
  have hmeas : MeasurableSet {p : (UPos n r → 𝔸[K]) × normOneGL K n |
      mk Γ₁ (unipOne K n r p.1 * p.2) ∉ Z'} :=
    ((measurableSet_toMeasurable _ _).preimage ((measurable_mk Γ₁).comp
      (continuous_unipOne_mul r).measurable)).compl
  have h1 : ∀ᵐ X ∂unipMeasure K n r, ∀ᵐ y ∂μ, mk Γ₁ (unipOne K n r X * y) ∉ Z' := by
    refine Eventually.of_forall fun X => ?_
    rw [ae_iff]
    simp only [not_not]
    have := measure_preimage_mul μ (unipOne K n r X) (mk Γ₁ ⁻¹' Z')
    rw [(quasiMeasurePreserving_mk Γ₁ μ).preimage_null hZ'] at this
    exact this
  have h2 := (Measure.ae_ae_comm hmeas).1 h1
  filter_upwards [h2] with y hy
  filter_upwards [hy] with X hX
  exact fun h => hX (subset_toMeasurable _ _ h)

theorem ae_ctFun_congr (r : ℕ) {F F' : RightCosetSpace Γ₁ → ℂ}
    (h : F =ᵐ[quotientMeasure Γ₁ μ] F') : ∀ᵐ y ∂μ, ctFun K n r F y = ctFun K n r F' y := by
  have hZ : quotientMeasure Γ₁ μ {x | F x ≠ F' x} = 0 := ae_iff.1 h
  filter_upwards [ae_ae_unip_notMem μ hZ r] with y hy
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hy] with X hX
  simpa using hX

theorem ae_integrableOn_unip (r : ℕ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, IntegrableOn (fun X => φ (mk Γ₁ (unipOne K n r X * y)))
      (unipFundamentalDomain K n r) (unipMeasure K n r) := by
  have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
      ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
    ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
      (continuous_unipOne_mul r).measurable)).enorm
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
  have hfin : ∫⁻ y in S, ∫⁻ X in unipFundamentalDomain K n r,
      ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r ∂μ ≠ ⊤ := by
    refine (L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt ?_)).ne
    exact ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)
  have hm2 : Measurable fun y => ∫⁻ X in unipFundamentalDomain K n r,
      ‖φ (mk Γ₁ (unipOne K n r X * y))‖ₑ ∂unipMeasure K n r :=
    hmeas.lintegral_prod_left'
  filter_upwards [ae_lt_top' hm2.aemeasurable hfin] with y hy
  refine ⟨?_, hy⟩
  exact ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk Γ₁).comp
    ((continuous_unipOne_mul r).comp (continuous_id.prodMk continuous_const)).measurable)).aestronglyMeasurable

theorem stronglyMeasurable_ctFun (r : ℕ) {F : RightCosetSpace Γ₁ → ℂ} (hF : StronglyMeasurable F) :
    StronglyMeasurable (ctFun K n r F) := by
  have : StronglyMeasurable (uncurry fun (X : UPos n r → 𝔸[K]) (y : normOneGL K n) =>
      F (mk Γ₁ (unipOne K n r X * y))) :=
    hF.comp_measurable ((measurable_mk Γ₁).comp (continuous_unipOne_mul r).measurable)
  exact this.integral_prod_left (μ := (unipMeasure K n r).restrict (unipFundamentalDomain K n r))

theorem ae_constantTermL2_add (r : ℕ) (φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, constantTermL2 μ r (φ + ψ) y = constantTermL2 μ r φ y + constantTermL2 μ r ψ y := by
  filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_add φ ψ), ae_integrableOn_unip μ r φ,
    ae_integrableOn_unip μ r ψ] with y h1 h2 h3
  rw [constantTermL2, h1]
  simp only [constantTermL2, ctFun, Pi.add_apply]
  exact integral_add h2 h3

theorem ae_constantTermL2_smul (r : ℕ) (c : ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, constantTermL2 μ r (c • φ) y = c * constantTermL2 μ r φ y := by
  filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_smul c φ)] with y h1
  rw [constantTermL2, h1, ctFun, constantTermL2, ctFun, ← integral_const_mul]
  rfl

theorem ae_constantTermL2_sub (r : ℕ) (φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    ∀ᵐ y ∂μ, constantTermL2 μ r (φ - ψ) y = constantTermL2 μ r φ y - constantTermL2 μ r ψ y := by
  filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_sub φ ψ), ae_integrableOn_unip μ r φ,
    ae_integrableOn_unip μ r ψ] with y h1 h2 h3
  rw [constantTermL2, h1]
  simp only [constantTermL2, ctFun, Pi.sub_apply]
  exact integral_sub h2 h3

theorem exists_lintegral_constantTermL2_sq_le (r : ℕ) {S : Set (normOneGL K n)} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      (∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ) ^ 2 ≤ C * ‖φ‖ₑ ^ 2 := by
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
  refine ⟨C, hC, fun φ => le_trans ?_ (hCφ φ)⟩
  gcongr with y
  exact enorm_integral_le_lintegral_enorm _

instance isMulRightInvariant_haar : μ.IsMulRightInvariant := isMulRightInvariant_normOneGL μ

def IsCuspidalL2 (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) : Prop :=
  ∀ r : ℕ, 0 < r → r < n → constantTermL2 μ r φ =ᵐ[μ] 0

def cuspidalL2 : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)) where
  carrier := {φ | IsCuspidalL2 μ φ}
  zero_mem' := fun r _ _ => by
    filter_upwards [ae_ctFun_congr μ r (Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ))] with y hy
    rw [constantTermL2, hy]
    simp [ctFun]
  add_mem' := fun {φ ψ} hφ hψ r hr hrn => by
    filter_upwards [ae_constantTermL2_add μ r φ ψ, hφ r hr hrn, hψ r hr hrn] with y h1 h2 h3
    rw [h1, h2, h3]
    simp
  smul_mem' := fun c φ hφ r hr hrn => by
    filter_upwards [ae_constantTermL2_smul μ r c φ, hφ r hr hrn] with y h1 h2
    rw [h1, h2]
    simp

theorem mem_cuspidalL2 {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} : φ ∈ cuspidalL2 μ ↔ IsCuspidalL2 μ φ :=
  Iff.rfl

theorem isClosed_cuspidalL2 : IsClosed (cuspidalL2 μ : Set (Lp ℂ 2 (quotientMeasure Γ₁ μ))) := by
  refine isClosed_of_closure_subset fun φ hφ r hr hrn => ?_
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ
  have hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2 := by
    intro ε hε
    obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.1 hφ ε hε
    have hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [ae_constantTermL2_sub μ r φ ψ, (hψ : IsCuspidalL2 μ ψ) r hr hrn] with y h1 h2
      rw [h1, h2, Pi.zero_apply, sub_zero]
    rw [hI]
    refine (hCφ (φ - ψ)).trans ?_
    gcongr
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hdist.le
  have hI0 : I ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    have ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have := (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  have hI' : I = 0 := pow_eq_zero_iff two_ne_zero |>.1 hI0
  have hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S) :=
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.enorm.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy
  simpa using hy

theorem isInvariant_cuspidalL2 : (rightRegularRep Γ₁ μ).IsInvariant (cuspidalL2 μ) := by
  intro g φ hφ r hr hrn
  have h2 := ae_ctFun_congr μ r (coeFn_rightRegularRep Γ₁ μ g φ)
  have h3 : ∀ y, ctFun K n r (fun z => φ (rightMul Γ₁ g z)) y = constantTermL2 μ r φ (y * g) := by
    intro y
    simp only [ctFun, constantTermL2, rightMul_mk, mul_assoc]
  have h4 : ∀ᵐ y ∂μ, constantTermL2 μ r φ (y * g) = 0 :=
    (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae ((hφ : IsCuspidalL2 μ φ) r hr hrn)
  filter_upwards [h2, h4] with y hy1 hy2
  rw [constantTermL2, hy1, h3, hy2, Pi.zero_apply]

theorem integral_rconv_unip_eq_zero (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    (x : normOneGL K n) :
    ∫ X in unipFundamentalDomain K n r, rconv Γ₁ μ f φ (unipOne K n r X * x)
      ∂unipMeasure K n r = 0 := by
  set S := (x * ·) '' tsupport (f : normOneGL K n → ℂ)
  have hS : IsCompact S := f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hfS : ∀ z ∉ S, f (x⁻¹ * z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨x⁻¹ * z, h, by simp⟩
  set F : (UPos n r → 𝔸[K]) → normOneGL K n → ℂ :=
    fun X z => f (x⁻¹ * z) * φ (mk Γ₁ (unipOne K n r X * z))
  have hFm : StronglyMeasurable (uncurry F) :=
    (f.continuous.comp (continuous_const_mul x⁻¹ |>.comp continuous_snd)).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk Γ₁).comp
        (continuous_unipOne_mul r).measurable))
  have hint : Integrable (uncurry F)
      (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
    have hfin : ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ < ⊤ :=
      L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt
        (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)))
    have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
        ‖φ (mk Γ₁ (unipOne K n r p.1 * p.2))‖ₑ :=
      ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk Γ₁).comp
        (continuous_unipOne_mul r).measurable)).enorm
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.aestronglyMeasurable.enorm]
    calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z, ‖uncurry F (X, z)‖ₑ ∂μ ∂unipMeasure K n r
        ≤ ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z in S,
            ENNReal.ofReal M * ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂μ ∂unipMeasure K n r := by
          refine lintegral_mono fun X => ?_
          rw [← lintegral_indicator hS.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ S
          · rw [indicator_of_mem hz]
            simp only [F, uncurry_apply_pair, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM _)
          · rw [indicator_of_notMem hz]
            simp [F, hfS z hz]
      _ = ENNReal.ofReal M * ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
            ‖φ (mk Γ₁ (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_lintegral_swap hmeas.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hinner : ∀ X, rconv Γ₁ μ f φ (unipOne K n r X * x) = ∫ z, F X z ∂μ := by
    intro X
    rw [rconv, ← integral_mul_left_eq_self _ (unipOne K n r X)]
    congr 1
    ext z
    simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hCT : ∀ z, ∫ X in unipFundamentalDomain K n r, F X z ∂unipMeasure K n r =
      f (x⁻¹ * z) * constantTermL2 μ r φ z := by
    intro z
    simp only [F, constantTermL2, ctFun]
    exact integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_integral_swap hint]
  simp_rw [hCT]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(hφ : IsCuspidalL2 μ φ) r hr hrn] with z hz
  rw [hz, Pi.zero_apply, mul_zero]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
