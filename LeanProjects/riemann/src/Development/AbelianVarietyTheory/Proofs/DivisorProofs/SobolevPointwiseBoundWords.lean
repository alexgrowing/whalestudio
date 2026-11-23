import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSlice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntervalIntegralLeMulIntervalIntegralSq
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.SliceSob

section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def dw (l : List V) (g : V → ℂ) : V → ℂ :=
  l.foldr (fun e u y => fderiv ℝ u y e) g

theorem contDiff_dw (l : List V) {g : V → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (dw l g) := by
  induction l with
  | nil => exact hg
  | cons e l ih =>
    exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_line {u : V → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x e : V) (t : ℝ) :
    HasDerivAt (fun r : ℝ => u (x + r • e)) (fderiv ℝ u (x + t • e) e) t := by
  have h1 : HasDerivAt (fun r : ℝ => x + r • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  exact ((hu.differentiable (by simp)) (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1

theorem step {u : V → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x e : V) :
    ‖u x‖ ^ 2 ≤ (2 * ∫ r in (0:ℝ)..1, ‖u (x + r • e)‖ ^ 2) +
      2 * ∫ r in (0:ℝ)..1, ‖fderiv ℝ u (x + r • e) e‖ ^ 2 := by
  have hc : Continuous (dw [e] u) := (contDiff_dw [e] hu).continuous
  have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun r : ℝ => u (x + r • e))
    (fun r : ℝ => fderiv ℝ u (x + r • e) e) 1 one_pos (fun t _ => hasDerivAt_line hu x e t)
    (hc.comp (f := fun r : ℝ => x + r • e) (by fun_prop)).continuousOn
  simpa using this

theorem sobolev_haar [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {D : ℕ} (b : Module.Basis (Fin D) ℝ V) :
    ∃ C : ℝ, ∀ g : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ S : ENNReal,
      (∀ l : List (Fin D), l.length ≤ D → ∫⁻ y, ‖dw (l.map b) g y‖ₑ ^ 2 ∂μ ≤ S) →
      ‖g 0‖ₑ ^ 2 ≤ ENNReal.ofReal C * S := by
  let T : (Fin D → ℝ) ≃L[ℝ] V := b.equivFunL.symm
  have hT : ∀ t, T t = ∑ i, t i • b i := fun t => b.equivFun_symm_apply t
  let ν : Measure V := Measure.map T volume
  haveI : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map _
  let c : ℝ≥0 := Measure.addHaarScalarFactor ν μ
  have hν : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  refine ⟨4 ^ D * (c + 1), fun g hg S hS => ?_⟩
  have hpos : (0:ℝ) < 4 ^ D * (c + 1) := by positivity
  rcases eq_or_ne S ⊤ with rfl | hS'
  · rw [ENNReal.mul_top (by simpa using hpos)]; exact le_top
  have key := GlobalTheory.ThetaGrowth.sobolev_iter D 0 (fun i r => r • b i)
    (fun p => {u | ∃ l : List (Fin D), l.length ≤ p ∧ u = dw (l.map b) g}) (c * S.toReal) (0 : V)
    (fun i => by fun_prop)
    (fun p q hpq u ⟨l, hl, hu⟩ => ⟨l, hl.trans hpq, hu⟩)
    (by
      rintro p u ⟨l, hl, rfl⟩
      refine ⟨(contDiff_dw _ hg).continuous, fun i => ⟨dw ((i :: l).map b) g,
        ⟨i :: l, by simpa using hl, rfl⟩, fun x => ?_⟩⟩
      exact step (contDiff_dw _ hg) x (b i))
    (by
      rintro u ⟨l, hl, rfl⟩
      have hcu : Continuous (dw (l.map b) g) := (contDiff_dw _ hg).continuous
      have h1 := hS l (by simpa using hl)
      set u := dw (l.map b) g
      simp only [zero_add, ← hT]
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
        (Continuous.aestronglyMeasurable (by fun_prop))]
      have h2 : ∫⁻ t in Set.univ.pi fun _ => Set.Icc (0:ℝ) 1, ENNReal.ofReal (‖u (T t)‖ ^ 2)
          ≤ c * S := by
        calc _ ≤ ∫⁻ t, ENNReal.ofReal (‖u (T t)‖ ^ 2) := setLIntegral_le_lintegral _ _
          _ = ∫⁻ t, ‖u (T t)‖ₑ ^ 2 := by
            refine lintegral_congr fun t => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          _ = ∫⁻ y, ‖u y‖ₑ ^ 2 ∂ν := by
            rw [lintegral_map (hcu.measurable.enorm.pow_const 2) T.continuous.measurable]
          _ = c * ∫⁻ y, ‖u y‖ₑ ^ 2 ∂μ := by
            rw [hν, lintegral_smul_measure]; rfl
          _ ≤ c * S := by gcongr
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hS') h2
      simpa using this)
    g ⟨[], le_rfl, rfl⟩
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_toReal hS', ← ENNReal.ofReal_mul hpos.le]
  refine ENNReal.ofReal_le_ofReal (key.trans ?_)
  rw [mul_assoc]
  gcongr
  linarith

theorem exists_small_basis [FiniteDimensional ℝ V] :
    ∃ (D : ℕ) (b : Module.Basis (Fin D) ℝ V), ∀ i, ‖b i‖ ≤ 1 := by
  let b := Module.finBasis ℝ V
  have h : ∀ i, (‖b i‖⁻¹ : ℝ) ≠ 0 := fun i => inv_ne_zero (norm_ne_zero_iff.2 (b.ne_zero i))
  refine ⟨_, b.unitsSMul fun i => Units.mk0 _ (h i), fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (b.ne_zero i))]

end General

open GlobalTheory.SobClass

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem contDiff_slice {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (x : κ → AF F) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => Φ (x + archInc F y) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    have e : (fun y => pureA F f g (x + archInc F y)) = fun y =>
        f ((fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1) + y) *
          g (fun i => (x i).2) := by
      funext y
      unfold pureA
      congr 2
      · funext i
        change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 +
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = _
        rw [map_add, RingEquiv.apply_symm_apply]; rfl
      · funext i
        change (x i).2 + (archInc F y i).2 = _
        rw [archInc_snd, add_zero]
    rw [e]
    exact ((f.smooth ⊤).comp (contDiff_const.add contDiff_id)).mul contDiff_const
  | zero => exact contDiff_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact contDiff_const.mul h

theorem realAd_smul_archInc (t : ℝ) (e : κ → mixedEmbedding.mixedSpace F) :
    realAd F t • archInc F e = archInc F (t • e) := by
  funext i
  refine Prod.ext ?_ ?_
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (e i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e i)
    rw [← map_mul, Algebra.smul_def]
  · change (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    rw [mul_zero]

theorem word_slice (ψ : AddChar (AF F) ℂ) {Φ : (κ → AF F) → ℂ} (x : κ → AF F)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) fun y => Φ (x + archInc F y))
    (l : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun y => wordH ψ (l.map fun e => (archInc F e, 0)) Φ (x + archInc F y)) =
      dw l fun y => Φ (x + archInc F y) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    funext y
    have h := (hasDerivAt_line (contDiff_dw l hΦ) y e 0).deriv
    rw [zero_smul, add_zero] at h
    refine Eq.trans ?_ h
    change deriv (fun t : ℝ => schr ψ (realAd F t • (archInc F e, 0))
      (wordH ψ (l.map fun e => (archInc F e, 0)) Φ) (x + archInc F y)) 0 = _
    congr 1
    funext t
    rw [← ih]
    simp only [schr, Prod.smul_mk, smul_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul, realAd_smul_archInc, archInc_add, add_assoc]

theorem slice_sobolev : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (D : ℕ) (C : ℝ), (∀ l ∈ L, l.length ≤ D ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ Φ ∈ schA F κ, ∀ x : κ → AF F, ‖Φ x‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∑ l ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + GlobalTheory.SobClass.archInc F y)‖ₑ ^ 2 := by
  intro F _ _ κ _ ψ _
  obtain ⟨D, b, hb⟩ := exists_small_basis (V := κ → mixedEmbedding.mixedSpace F)
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  haveI : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  obtain ⟨C, hC⟩ := sobolev_haar (volume : Measure (κ → mixedEmbedding.mixedSpace F)) b
  let L₀ : Finset (List (Fin D)) := (List.finite_length_le (Fin D) D).toFinset
  refine ⟨L₀.image fun l => (l.map b).map fun e => (archInc F e, 0), D, C, ?_, ?_⟩
  · intro l hl
    obtain ⟨l, hl', rfl⟩ := Finset.mem_image.1 hl
    refine ⟨by simpa [L₀] using hl', fun w hw => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
    exact isArchUnit_der _ fun i => (norm_le_pi_norm _ i).trans (hb j)
  · intro Φ hΦ x
    have h0 : archInc F (0 : κ → mixedEmbedding.mixedSpace F) = 0 := by
      have := archInc_add (F := F) (κ := κ) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    have := hC _ (contDiff_slice hΦ x) (∑ l ∈ L₀.image fun l => (l.map b).map
        fun e => ((archInc F e, 0) : (κ → AF F) × (κ → AF F)),
        ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + archInc F y)‖ₑ ^ 2)
      (fun l hl => by
        rw [← word_slice ψ x (contDiff_slice hΦ x)]
        exact Finset.single_le_sum (f := fun l => ∫⁻ y : κ → mixedEmbedding.mixedSpace F,
          ‖wordH ψ l Φ (x + archInc F y)‖ₑ ^ 2) (fun _ _ => zero_le)
          (Finset.mem_image_of_mem _ (by simpa [L₀] using hl)))
    simpa only [h0, add_zero] using this

end GlobalTheory.SliceSob
