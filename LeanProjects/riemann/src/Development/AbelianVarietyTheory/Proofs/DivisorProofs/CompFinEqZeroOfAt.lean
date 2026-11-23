import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

noncomputable section

namespace GlobalTheory.ThK.FiniteLevelDerivatives

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem compFin_eq_zero_of_at {x : AE F E} (hx : At (evI F) x) (v : HeightOneSpectrum (𝓞 F)) : compFin F E v x = 0 := by
  let u : AF F := (0, 1)
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h0 : u • x = 0 := hx u hu
  have hs : compFin F E v (algebraMap (AF F) (AE F E) u) = 1 := by
    have h2 : sndA F u = 1 := rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (u ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.map_tmul, evFin, AlgHom.comp_apply, h2, map_one, AlgHom.id_apply]
    rfl
  have h1 := congrArg (compFin F E v) h0
  rwa [Algebra.smul_def, map_mul, hs, one_mul, map_zero] at h1

theorem toGAd_mem_infPts (hσ : ∀ x, σ (σ x) = x) {d : ℕ} (W : Spc F E d) {c : E} (hc : c ≠ 0) {k : UA σ W.J}
    (hk : k ∈ UAt σ W (evI F)) : toGAd hσ W.J hc k ∈ infPts σ (c • W.J.map σ) := by
  rw [mem_infPts_iff_forall]
  intro v
  apply matHom_injective
  rw [matHom_proj, map_one]
  apply Units.ext
  show (mat k).map (compFin F E v) = 1
  ext i j
  have h : At (evI F) ((mat k - 1) i j) := fun u hu => congrFun (congrFun (hk u hu) i) j
  have h1 := compFin_eq_zero_of_at h v
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

end GlobalTheory.ThK.FiniteLevelDerivatives

end
