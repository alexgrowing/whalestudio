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

namespace GlobalTheory.UnipEmb.PlaceSpan

theorem locInc_mul_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v ⊗[F] E) (e : E) :
    GlobalTheory.UnipEmb.locInc F E v (a * inclR (Fv F v) e) = GlobalTheory.UnipEmb.locInc F E v a * inclR (AF F) e := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, add_mul]
  | tmul b e' =>
    simp [GlobalTheory.UnipEmb.locInc, inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem locInc_splitIncl_mem_colSpan : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (u : Fin n → Fv F v),
    u ∈ Submodule.span (Fv F v) ((fun i k => τ (X k i)) '' I) →
    (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ u k)) ∈ GlobalTheory.StdPar.colSpan F X I := by
  intro F E _ _ _ _ _ σ h v τ n r X I u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have e : (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ (fun k => τ (X k i)) k)) =
        GlobalTheory.UnipEmb.locInc F E v (splitIdem h τ) • (adMat F X)ᵀ i := by
      funext k
      have : splitIncl h τ (fun k => τ (X k i)) k = splitIdem h τ * inclR (Fv F v) (X k i) := by
        rw [splitIdem_mul, splitProj_inclR]; rfl
      rw [this, locInc_mul_inclR]
      simp [adMat]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  | zero =>
    have e : (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ (0 : Fin n → Fv F v) k)) = 0 := by
      funext k; simp [splitIncl]
    rw [e]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ (x + y) k)) =
        (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ x k)) +
          (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ y k)) := by
      funext k; simp [splitIncl, add_smul]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ (c • x) k)) =
        GlobalTheory.UnipEmb.locInc F E v (c ⊗ₜ[F] (1 : E)) • (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ x k)) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, splitIncl]
      rw [← map_mul, mul_smul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [e]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.UnipEmb.PlaceSpan
