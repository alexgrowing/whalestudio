import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix

namespace GlobalTheory

theorem colPerp_conj_place_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {r : ℕ} (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r))
    (y : Fin n → AF F ⊗[F] E), y ∈ GlobalTheory.StdPar.colPerp σ J X I → ∀ (i : Fin r), i ∈ I →
    (fun k => splitProj (τ.comp σ) (compFin F E v (y k))) ⬝ᵥ (J.map τ *ᵥ fun k => τ (X k i)) = 0 := by
  intro F E _ _ _ _ _ σ h n J hJ v τ r X I y hy i hi
  simp only [GlobalTheory.StdPar.colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  have h0 := hy i hi
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.proj_apply] at h0
  have h1 := congrArg (fun z => splitProj (τ.comp σ) (compFin F E v z)) h0
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero, Matrix.map_apply] at h1
  have hc : ∀ e : E, compFin F E v (inclR (AF F) e) = inclR (Fv F v) e := by
    intro e
    simp [compFin, inclR]
  have hcc := comp_conj_conj h τ
  have hs : ∀ e : E, τ (σ (σ e)) = τ e := fun e => by
    simpa using congrArg (fun f : E →ₐ[F] Fv F v => f e) hcc
  simp only [hc, splitProj_inclR] at h1
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul] at h1
  simp only [AlgHom.comp_apply, RingHom.coe_coe, hs, hJ.1] at h1
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end GlobalTheory
