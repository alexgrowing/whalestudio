import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicGLMulVecHaarEqModulusDet

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def colv (m : ℕ) (bs : Module.Basis (Fin 2) F E) : (Fin m × Fin 2 → AF F) ≃ₜ+ (Fin m → AE F E) :=
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  { toFun v a := cmbE bs fun t => v (a, t)
    invFun z p := (Algebra.TensorProduct.basis (AF F) bs).repr (z p.1) p.2
    left_inv v := by
      funext p
      exact repr_cmbE_apply bs _ p.2
    right_inv z := by
      funext a
      exact cmbE_repr bs (z a)
    map_add' v w := by
      funext a
      simp only [cmbE, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    continuous_toFun := by
      refine continuous_pi fun a => ?_
      have h : (fun v : Fin m × Fin 2 → AF F => cmbE bs fun t => v (a, t)) =
          (GlobalTheory.JacSubst.coordCE F E bs).symm ∘ fun v t => v (a, t) := by
        funext v
        simp only [Function.comp_apply, cmbE_eq]
        change _ = (Algebra.TensorProduct.basis (AF F) bs).equivFun.symm (fun t => v (a, t))
        rw [Module.Basis.equivFun_symm_apply]
      rw [h]
      exact (GlobalTheory.JacSubst.coordCE F E bs).symm.continuous.comp (continuous_pi fun t => continuous_apply _)
    continuous_invFun := by
      refine continuous_pi fun p => ?_
      exact (continuous_apply p.2).comp ((GlobalTheory.JacSubst.coordCE F E bs).continuous.comp (continuous_apply p.1)) }

theorem Lc_eq_colv {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (v : Fin m × Fin 2 → AF F) : Lc bs M v = (colv m bs).symm (M *ᵥ colv m bs v) := rfl

def HaarLc : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∀ (bs : Module.Basis (Fin 2) F E) (g : UA σ J)
    (μ : @Measure (Fin m × Fin 2 → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f : (Fin m × Fin 2 → AF F) → ℝ≥0∞, ∫⁻ x, f (Lc bs (mat g) x) ∂μ = ∫⁻ x, f x ∂μ

end PositivityTheory.SiegelWeilFormula.Ald

end
