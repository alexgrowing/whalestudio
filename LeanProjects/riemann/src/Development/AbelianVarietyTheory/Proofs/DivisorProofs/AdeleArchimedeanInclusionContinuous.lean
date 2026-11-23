import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct

namespace GlobalTheory.DecCont

theorem continuous_symm_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], NumberField.IsTotallyReal F → ∀ Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ u : AdeleRing (𝓞 F) F, u.2 = 0 → Φ (algebraMap (AdeleRing (𝓞 F) F) (AE F E) u) = (fun w => InfinitePlace.Completion.extensionEmbedding w (u.1 w), 0)) → Continuous (fun c : InfinitePlace F → ℂ => Φ.symm (c, 0)) := by
  intro F E _ _ _ _ _ hF Φ hΦ
  classical
  haveI : IsModuleTopology (AdeleRing (𝓞 F) F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AdeleRing (𝓞 F) F) _
  haveI : ContinuousSMul (AdeleRing (𝓞 F) F) (AE F E) :=
    IsModuleTopology.toContinuousSMul (AdeleRing (𝓞 F) F) _
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  let rr : InfinitePlace F → ℝ → AdeleRing (𝓞 F) F := fun w t =>
    ((Pi.single w ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm t) :
      InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  have hrc : ∀ w, Continuous (rr w) := fun w =>
    ((continuous_single w).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous).prodMk
      continuous_const
  have he : ∀ (w : InfinitePlace F) (t : ℝ), InfinitePlace.Completion.extensionEmbedding w
      ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm t) = t := fun w t =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hr w) _).symm.trans
      (congrArg _ ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).apply_symm_apply t))
  have key : ∀ (w : InfinitePlace F) (t : ℝ) (z : ℂ),
      Φ (rr w t • Φ.symm (Pi.single w z, 0)) = (Pi.single w ((t : ℂ) * z), 0) := by
    intro w t z
    rw [Algebra.smul_def, map_mul, hΦ _ rfl, Φ.apply_symm_apply, Prod.mk_mul_mk, mul_zero]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv
      rw [Pi.mul_apply]
      simp only [rr, Pi.single_eq_same, he, mul_one]
    · simp [rr, Pi.single_eq_of_ne hv]
  have hsum : (fun c : InfinitePlace F → ℂ => Φ.symm (c, 0)) = fun c =>
      ∑ w, (rr w (c w).re • Φ.symm (Pi.single w 1, 0) +
        rr w (c w).im • Φ.symm (Pi.single w Complex.I, 0)) := by
    funext c
    apply Φ.injective
    rw [Φ.apply_symm_apply, map_sum]
    simp only [map_add, key]
    ext v
    · rw [Prod.fst_sum, Finset.sum_apply]
      simp only [Prod.fst_add, mul_one, Pi.add_apply, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      exact (Complex.re_add_im _).symm
    · rw [Prod.snd_sum]
      simp
  rw [hsum]
  refine continuous_finset_sum _ fun w _ => ?_
  exact ((hrc w).comp (Complex.continuous_re.comp (continuous_apply w))).smul continuous_const |>.add
    (((hrc w).comp (Complex.continuous_im.comp (continuous_apply w))).smul continuous_const)

end GlobalTheory.DecCont
