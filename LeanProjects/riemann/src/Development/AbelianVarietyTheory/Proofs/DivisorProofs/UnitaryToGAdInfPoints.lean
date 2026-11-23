import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.SquareIntegrability

theorem toGAd_mem_infPts_of_uAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (W : Spc F E d) (c : E) (hc : c ≠ 0) :
    ∀ g ∈ UAt σ W (evI F), toGAd hσ W.J hc g ∈ infPts σ (c • W.J.map σ) := by
  intro g hg
  unfold infPts
  rw [MonoidHom.mem_ker]
  let u : AF F := (0, 1)
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  have h := hg u hu
  set φ := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
  have hsu : sndA F u = 1 := rfl
  have key : ∀ x : TensorProduct F (AF F) E, φ (u • x) = φ x := by
    intro x
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.map_tmul, hsu, AlgHom.id_apply, Algebra.TensorProduct.one_def.symm, one_mul]
  apply Units.ext
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply] at hij
  have e1 : φ ((mat g) i j - (1 : Matrix (Fin d) (Fin d) (TensorProduct F (AF F) E)) i j) = 0 := by
    rw [← key, hij, map_zero]
  rw [map_sub, sub_eq_zero] at e1
  change φ ((mat g) i j) = (1 : Matrix (Fin d) (Fin d) (TensorProduct F (Af F) E)) i j
  rw [e1]
  by_cases hij' : i = j
  · subst hij'; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij']

end GlobalTheory.ThK.SquareIntegrability
