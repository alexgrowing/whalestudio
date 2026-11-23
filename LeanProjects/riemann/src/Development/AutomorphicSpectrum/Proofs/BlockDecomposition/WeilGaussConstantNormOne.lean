import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
open Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.Right

section Norm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

omit [ValuativeRel E] in

theorem mem_valBall_of_modulus_lt {d : F} {n : ℤ} (h : modulus d < (residueCard F : ℝ≥0) ^ (-n)) :
    d ∈ valBall F n := by
  by_cases h0 : d = 0
  · subst h0; exact zero_mem _
  rw [mem_valBall_iff_le_ord h0]
  rw [modulus_of_ne_zero h0] at h
  have := (zpow_lt_zpow_iff_right₀ one_lt_residueCard_nnreal).1 h
  omega

variable (F) in

theorem continuous_normE : Continuous (fun z : E => Algebra.norm F z) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : Continuous (fun z : E => z * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E z
      - x * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E x) :=
    (continuous_id.mul GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj).sub continuous_const
  have hm := (continuous_modulus (K := E)).comp hc
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, hasBasis_nhds_zero_valBall.tendsto_right_iff]
  intro n _
  have hq : (0 : ℝ≥0) < (residueCard F : ℝ≥0) ^ (-n) :=
    zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _
  have ht : Tendsto (fun z : E => modulus (z * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E z
      - x * GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E x)) (𝓝 x) (𝓝 0) := by
    simpa [Function.comp_def] using hm.tendsto x
  have hev := ht.eventually (gt_mem_nhds (pow_pos hq 2))
  filter_upwards [hev] with z hz
  refine mem_valBall_of_modulus_lt ?_
  have hz' : modulus (algebraMap F E (Algebra.norm F z - Algebra.norm F x)) <
      ((residueCard F : ℝ≥0) ^ (-n)) ^ 2 := by
    rw [map_sub, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.algebraMap_norm_eq_mul_conj,
      GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.algebraMap_norm_eq_mul_conj]
    exact hz
  rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap] at hz'
  exact lt_of_pow_lt_pow_left₀ 2 zero_le hz'

end Norm

def kern (E : Type) [Field E] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra F E] (χ : AddChar F Circle) (g : F → ℂ) (Φ : E → ℂ)
    (p : F × E) : ℂ :=
  g p.1 * nsg E p.1 * (((modulus p.1 : ℝ)⁻¹ : ℝ) : ℂ) *
    ((χ (-(Algebra.norm F p.2) / p.1) : ℂ) * Φ p.2)

section Kernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem continuousAt_nsg {η : Fˣ →* ℂˣ} (hηc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {a : F} (ha : a ≠ 0) :
    ContinuousAt (nsg E : F → ℂ) a := by
  have hcomp : Continuous ((nsg E : F → ℂ) ∘ (Units.val : Fˣ → F)) := by
    have : ((nsg E : F → ℂ) ∘ (Units.val : Fˣ → F)) = fun u => ((η u : ℂˣ) : ℂ) := by
      funext u; exact (hη u).symm
    rw [this]
    exact Units.continuous_val.comp hηc
  have hoe : IsOpenEmbedding (Units.val : Fˣ → F) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have hr : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
      ext x
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro h
        exact ⟨Units.mk0 x h, rfl⟩
    rw [hr]
    exact isOpen_compl_singleton
  have := hoe.continuousAt_iff (g := (nsg E : F → ℂ)) (x := Units.mk0 a ha)
  simpa using this.1 hcomp.continuousAt

theorem continuous_kern {χ : AddChar F Circle} (hχ : Continuous χ) {η : Fˣ →* ℂˣ}
    (hηc : Continuous η) (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {Φ : E → ℂ}
    (hΦ : Continuous Φ) {g : F → ℂ} (hg : IsLocallyConstant g) (hg0 : g 0 = 0) :
    Continuous (kern E χ g Φ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, z⟩
  by_cases ha : a = 0
  · subst ha
    have hopen : {b : F | g b = 0} ∈ 𝓝 (0 : F) :=
      (hg.isOpen_fiber 0).mem_nhds hg0
    have hev : kern E χ g Φ =ᶠ[𝓝 ((0 : F), z)] fun _ => 0 := by
      have := continuous_fst.continuousAt (x := ((0 : F), z)) hopen
      filter_upwards [this] with p hp
      have hp' : g p.1 = 0 := hp
      simp [kern, hp']
    exact (continuousAt_const (y := (0 : ℂ))).congr hev.symm
  · have h1 : ContinuousAt (fun p : F × E => g p.1) (a, z) :=
      (hg.continuous.comp continuous_fst).continuousAt
    have h2 : ContinuousAt (fun p : F × E => nsg E p.1) (a, z) :=
      ContinuousAt.comp (f := Prod.fst) (g := (nsg E : F → ℂ)) (continuousAt_nsg hηc hη ha)
        continuous_fst.continuousAt
    have h3 : ContinuousAt (fun p : F × E => (((modulus p.1 : ℝ)⁻¹ : ℝ) : ℂ)) (a, z) := by
      have hm : Continuous (fun p : F × E => ((modulus p.1 : ℝ≥0) : ℝ)) :=
        NNReal.continuous_coe.comp (continuous_modulus.comp continuous_fst)
      have hne : ((modulus a : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero ha
      exact Complex.continuous_ofReal.continuousAt.comp (hm.continuousAt.inv₀ hne)
    have h4 : ContinuousAt (fun p : F × E => -(Algebra.norm F p.2) / p.1) (a, z) :=
      (((continuous_normE F).comp continuous_snd).neg.continuousAt).div
        continuous_fst.continuousAt ha
    have h5 : ContinuousAt (fun p : F × E => (χ (-(Algebra.norm F p.2) / p.1) : ℂ)) (a, z) :=
      ContinuousAt.comp (g := fun x : F => (χ x : ℂ))
        (continuous_subtype_val.comp hχ).continuousAt h4
    have h6 : ContinuousAt (fun p : F × E => Φ p.2) (a, z) :=
      (hΦ.comp continuous_snd).continuousAt
    exact ((h1.mul h2).mul h3).mul (h5.mul h6)

theorem hasCompactSupport_kern {χ : AddChar F Circle} {Φ : E → ℂ} (hΦ : HasCompactSupport Φ)
    {g : F → ℂ} (hg : HasCompactSupport g) : HasCompactSupport (kern E χ g Φ) := by
  refine HasCompactSupport.intro (hg.isCompact.prod hΦ.isCompact) ?_
  rintro ⟨a, z⟩ hp
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [kern, image_eq_zero_of_notMem_tsupport h]
  · simp [kern, image_eq_zero_of_notMem_tsupport h]

end Kernel

theorem avg_fubini : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∫ a, g a * (nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) ∂selfDualMeasure χ = ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 η hηc hη Φ hΦ g hg hg0
  have hint : Integrable (kern E χ g Φ) ((selfDualMeasure χ).prod (muE E χ)) :=
    (continuous_kern hχ hηc hη hΦ.1.continuous hg.1 hg0).integrable_of_hasCompactSupport
      (hasCompactSupport_kern hΦ.2 hg.2)
  have hsw := integral_integral_swap (f := fun a z => kern E χ g Φ (a, z)) hint
  have hL : ∀ a : F, g a * (nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) =
      ∫ z, kern E χ g Φ (a, z) ∂muE E χ := by
    intro a
    simp only [kern]
    rw [integral_const_mul]
    ring
  have hR : ∀ z : E, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) =
      ∫ a, kern E χ g Φ (a, z) ∂selfDualMeasure χ := by
    intro z
    rw [GlobalTheory.CompanionTheory.GaussLam.hAvg, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [kern]
    ring
  simp only [hL, hR]
  exact hsw

end GlobalTheory.CompanionTheory.GaussLam.Right
