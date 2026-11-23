import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
noncomputable section

namespace GlobalTheory.ArchFamilyCont

theorem continuous_family : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ (f : SInf F (Fin n × Fin d)) y, Continuous fun t => T t f y) ∧
    ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure → ∀ f φ : SInf F (Fin n × Fin d),
      Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW γ hγ T hT
  classical
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hc : IsContOn (adeleClass F) om := hW.2.2
  have hline : Continuous fun t : ℝ => ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R) = tens (evI F) ⇑(T t f) R :=
    fun t f => hT t f R (hR f)
  have hRl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, R (liftV y) = R 0 := by
    intro y
    have hat : At (evI F) (liftV y) := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * liftV y i = 0
      exact Prod.ext (show u.1 * _ = 0 by rw [hu1, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
    have := (hR 0).1 0 (liftV y) hat
    simpa using this
  have hev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => evI F (liftV y i)) = y := by
    intro y; funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hfin : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => (liftV y i).2) = 0 := by
    intro y; funext i; rfl
  have htl : ∀ (f : SInf F (Fin n × Fin d)) y, tens (evI F) ⇑f R (liftV y) = f y * R 0 := by
    intro f y
    show f (fun i => evI F (liftV y i)) * R (liftV y) = _
    rw [hev, hRl]
  refine ⟨fun f y => ?_, fun μ hμ f φ => ?_⟩
  ·
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (liftV y)
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f' => ?_⟩
      show pureA F (⇑f') g (liftV y) = _
      simp only [pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
      have e1 := hev y
      have e2 := hfin y
      simp only [evI] at e1
      rw [e1, e2, mul_comm]
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => T t f y) = fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      show _ = tens (evI F) ⇑(T t f) R (liftV y) / R 0
      rw [htl, mul_div_cancel_right₀ _ hR0]
    rw [h3]
    exact h2.div_const _
  ·
    haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
    haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
    let Tφ : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
      (innerSL ℂ (φ.toLp 2 μ)).comp (SchwartzMap.toLpCLM ℂ ℂ 2 μ)
    have hTφ : ∀ g : SInf F (Fin n × Fin d), Tφ g = ∫ x, g x * starRingEnd ℂ (φ x) ∂μ := by
      intro g
      show inner ℂ (φ.toLp 2 μ) (g.toLp 2 μ) = _
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp φ 2 μ, SchwartzMap.coeFn_toLp g 2 μ] with x hx1 hx2
      rw [hx1, hx2, RCLike.inner_apply, mul_comm]
    let cL : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) :=
      { toFun := fun g => ⇑g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective cL := fun a b h => DFunLike.coe_injective h
    let eq := LinearEquiv.ofInjective cL hinj
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (Tφ.toLinearMap ∘ₗ eq.symm.toLinearMap)
    have hLc : ∀ g : SInf F (Fin n × Fin d), L ⇑g = Tφ g := by
      intro g
      have := LinearMap.congr_fun hL (eq g)
      simp at this
      exact this
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := L ∘ₗ LinearMap.funLeft ℂ ℂ liftV
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • Tφ, fun f' => ?_⟩
      have e : (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          = ⇑(g 0 • f') := by
        funext x
        have e1 := hev x
        have e2 := hfin x
        simp only [evI] at e1
        simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, SchwartzMap.smul_apply, smul_eq_mul]
        rw [e1, e2, mul_comm]
      show L (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g)) = _
      rw [e, hLc, map_smul]
      rfl
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) =
        fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      have e : (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R) :
          (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = ⇑(R 0 • T t f) := by
        funext x
        simp only [LinearMap.funLeft_apply, Function.comp_apply, SchwartzMap.smul_apply, smul_eq_mul]
        rw [htl, mul_comm]
      show _ = L (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R)) / R 0
      rw [e, hLc, map_smul, smul_eq_mul, hTφ, mul_div_cancel_left₀ _ hR0]
    rw [h3]
    exact h2.div_const _

end GlobalTheory.ArchFamilyCont
