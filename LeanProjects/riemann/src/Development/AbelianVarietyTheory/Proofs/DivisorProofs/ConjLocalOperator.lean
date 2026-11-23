import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.ConjLoc

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def conjSchR (κ : Type) [Fintype κ] : SInf F κ →L[ℝ] SInf F κ :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjSchR_apply {κ : Type} [Fintype κ] (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    conjSchR κ f x = starRingEnd ℂ (f x) := rfl

def conjSchCLM {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : SInf F κ →L[ℂ] SInf F κ₁) : SInf F κ →L[ℂ] SInf F κ₁ where
  toFun f := conjSchR κ₁ (T (conjSchR κ f))
  map_add' f g := by simp only [map_add]
  map_smul' c f := by
    have h : conjSchR κ (c • f) = starRingEnd ℂ c • conjSchR κ f := by
      refine SchwartzMap.ext fun y => ?_; simp only [conjSchR_apply, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
    refine SchwartzMap.ext fun x => ?_
    rw [h, map_smul, conjSchR_apply, RingHom.id_apply, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, Complex.conj_conj, conjSchR_apply]
  cont := (conjSchR κ₁).continuous.comp (T.continuous.comp (conjSchR κ).continuous)

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) :
    (fun x => starRingEnd ℂ (φ x)) ∈ SB X :=
  ⟨h.1.comp (starRingEnd ℂ), h.2.comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem conj_stdInd_apply (κ : Type) (v : Pl F) (y : κ → Fv F v) :
    starRingEnd ℂ (stdInd F κ v y) = stdInd F κ v y := by
  unfold stdInd
  by_cases hy : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
  · rw [Set.indicator_of_mem hy, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hy, map_zero]

theorem conj_stdInd (κ : Type) (v : Pl F) :
    (fun y => starRingEnd ℂ (stdInd F κ v y)) = stdInd F κ v :=
  funext (conj_stdInd_apply κ v)

theorem conj_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) x := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, conjSchR_apply, map_mul]
  congr 1
  exact MulEquiv.map_finprod (starRingAut : ℂ ≃+* ℂ).toMulEquiv _

theorem isLocOp_conjLin {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (he : IsLocOp e) : IsLocOp (conjLin e) := by
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  refine ⟨conjSchCLM ei, fun v => conjLin (ev v), fun v φ hφ => conj_mem_SB (hSB v _ (conj_mem_SB hφ)), ?_, ?_⟩
  · filter_upwards [hstd] with v hv
    funext y
    rw [conjLin_apply, conj_stdInd, hv, conj_stdInd_apply]
  · intro f φ hφ hfin
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) :=
      funext (conj_pure f φ)
    have hfin' : ∀ᶠ v in cofinite, (fun y => starRingEnd ℂ (φ v y)) = stdInd F κ v := by
      filter_upwards [hfin] with v hv
      rw [hv, conj_stdInd]
    rw [h1, hloc _ _ (fun v => conj_mem_SB (hφ v)) hfin', conj_pure]
    rfl

end GlobalTheory.DblEval.ConjLoc
