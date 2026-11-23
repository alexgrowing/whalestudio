import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.Reductions.ExistsSmoothFun

noncomputable section

namespace PositivityTheory.ThKR

open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKF PositivityTheory.ThKF.W PositivityTheory.ThKF.A GlobalTheory.HeisSchA GlobalTheory.RealWeil

theorem archLie' (hL : LocalLift) : PositivityTheory.ThKF.ArchLie := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ δ hδ T hT
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  let x : ℝ → UA σ X.J × UA σ W.J := fun t => (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))
  have xc : Continuous x := (hγ.1.comp continuous_ofAdd).prodMk (hδ.1.comp continuous_ofAdd)
  have x0 : x 0 = 1 := by simp [x]
  have xm : ∀ t u, x (t + u) = x t * x u := fun t u => by simp [x, ofAdd_add]
  have T0 : ∀ f, T 0 f = f := fun f => DFunLike.coe_injective (pureA_inj h₁ (by
    rw [← (hT 0).1 f _ h₀]
    exact (congrArg (fun y => om y _) x0).trans (LinearMap.congr_fun om.map_one _)))
  have Tm : ∀ t u f, T (t + u) f = T t (T u f) := fun t u f => DFunLike.coe_injective (pureA_inj h₁ (by
    rw [← (hT _).1 f _ h₀, ← (hT _).1 _ _ h₀, ← (hT _).1 f _ h₀]
    exact (congrArg (fun y => om y _) (xm t u)).trans (LinearMap.congr_fun (om.map_mul _ _) _)))
  have Tc : ∀ f (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ), Continuous fun t => L (T t f) := fun f L => by
    obtain ⟨l, hl, e⟩ := exists_adm L
    have := (hs.cont l hl _ (pureA_mem f h₀)).comp xc
    convert this using 1
    funext t
    show _ = l (om (x t) _)
    rw [(hT t).1 f _ h₀, e _ _ h₀, h₁, one_mul]
  have main := lie' hL (fun t => (C.P ≪≫ₗ phL M (x t) ≪≫ₗ C.P.symm).toLinearMap) (fun w => ?_) (fun w => ?_)
    (fun t u w => ?_) (fun t w w' => ?_) _ (fun t => impl_of hP C (T := (T t).toLinearMap) (hT t).1) (fun f => by simp [T0])
    (fun t u f => by simp [Tm]) (fun f lam => Tc (C.S.symm f) (lam.comp C.S.toContinuousLinearMap))
  · obtain ⟨Q, hQ, hd⟩ := main
    intro f hf
    have hw : ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, HasDerivAt (fun t => L (T t f)) (L (C.S.symm (Q (C.S f)))) 0 := fun L => by
      simpa using hd (C.S f) (L.comp (C.S.symm : _ →L[ℂ] _))
    refine ⟨C.S.symm (Q (C.S f)), ?_, ?_, hw⟩
    · refine weylAlg_induction (P := fun A => ∀ f ∈ M.Pol B.ψ B.emb, C.S.symm (A (C.S f)) ∈ M.Pol B.ψ B.emb)
        (fun f hf => by simpa using hf) (fun A w hA f hf => ?_) (fun f _ => by simp) (fun A A' h1 h2 f hf => ?_)
        (fun c A h1 f hf => ?_) hQ f hf
      · simpa [Coord.D] using hA _ (D_mem_Pol hP.base.std M C B.emb (C.P w) hf)
      · simpa using add_mem (h1 f hf) (h2 f hf)
      · simpa using Submodule.smul_mem _ c (h1 f hf)
    · refine actsD_of (T := fun t => T t f) (fun h => ⟨by simp [h], fun t => map_zero _⟩) (fun t => (hT t).1 f) fun y => ?_
      exact hw (BoundedContinuousFunction.evalCLM ℂ y ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _)
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, phL_eq]
    refine C.P.symm.toLinearMap.continuous_of_finiteDimensional.comp (continuous_infPart2.comp ?_)
    obtain ⟨u, hu⟩ := M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))
    simp only [← hu, phB_e]
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    refine (IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap).comp ?_
    exact ((Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp xc))).matrix_mul
      continuous_const).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp xc))).matrix_transpose
  · simp [phL_eq, x0, phB_one, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [phL_eq, xm, phB_mul, phL_spec, ← phL_eq]
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, C.sympl_eq, LinearEquiv.apply_symm_apply, tb_eq, ← phL_spec,
      phB_form]

end PositivityTheory.ThKR
