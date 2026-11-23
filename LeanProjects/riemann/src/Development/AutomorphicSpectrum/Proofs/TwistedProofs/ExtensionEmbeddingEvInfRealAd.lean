import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.CompanionTheory.RealAdeleComponent

open scoped TensorProduct
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem extensionEmbedding_evInf_realAd {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = (t : ℂ) := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)
  have e : evInf F w (realAd F t) = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)) w := rfl
  rw [e]
  generalize (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t) = y at h
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  by_cases hw : w.IsReal
  · have h1 := congrFun (congrArg Prod.fst h) ⟨w, hw⟩
    have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (y w) = t := h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, h2]
  · have h1 := congrFun (congrArg Prod.snd h) ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩
    exact h1

theorem piInf_realAd_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) (t : ℝ) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • x) = (t : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
  | tmul a e =>
    have h : ∀ b : AF F, piInf τ (b ⊗ₜ[F] e) =
        InfinitePlace.Completion.extensionEmbedding w (evInf F w b) * τ.1 e := fun b => rfl
    rw [TensorProduct.smul_tmul', smul_eq_mul, h, h, map_mul, map_mul, extensionEmbedding_evInf_realAd, mul_assoc]

end GlobalTheory.CompanionTheory.RealAdeleComponent

end
