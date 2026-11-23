import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSA
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_mul_conj {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E)) : (AE F E)ˣ) : AE F E) *
      cA σ ((Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E)) : (AE F E)ˣ) : AE F E) = 1 := by
  have h := congrArg Matrix.det (show ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have hu : IsUnit (incM F J).det := by
    have e : (incM F J).det = (inclR (F := F) (E := E) (AF F)) J.det := by
      rw [incM]
      exact (RingHom.map_det (inclR (F := F) (E := E) (AF F) : E →+* AE F E) J).symm
    rw [e]
    exact (Ne.isUnit hJ).map _
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  refine hu.mul_left_cancel ?_
  linear_combination h

theorem norm_det_unitary (hcm : IsCMExt F E σ) {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E))) = 1 := by
  obtain ⟨ξ, hq⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine Units.ext (hq.algebraMap_injective ?_)
  rw [Units.coe_map, Units.val_one, map_one]
  show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) _) = 1
  rw [hq.algebraMap_norm]
  exact det_mul_conj hJ g

end PositivityTheory.SiegelWeilFormula.Ald

end
