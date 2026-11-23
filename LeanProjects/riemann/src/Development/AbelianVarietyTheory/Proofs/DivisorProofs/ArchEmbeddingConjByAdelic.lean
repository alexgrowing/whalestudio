import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ConjArch

theorem conj_embArch (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (y : GArch σ J w) (b : GAd σ J) :
    b⁻¹ * embArch σ J w y * b = embArch σ J w ((projArch σ J w b)⁻¹ * y * projArch σ J w b) := by
  classical
  refine GAd_ext σ J (fun u => ?_) (fun v => ?_)
  · by_cases h : u = w
    · subst h
      simp only [map_mul, map_inv, projArch_embArch_self]
    · simp only [map_mul, map_inv, projArch_embArch_ne σ J h, mul_one, inv_mul_cancel, inv_one]
  · simp only [map_mul, map_inv, proj_embArch, mul_one, inv_mul_cancel, inv_one]

end GlobalTheory.ConjArch
