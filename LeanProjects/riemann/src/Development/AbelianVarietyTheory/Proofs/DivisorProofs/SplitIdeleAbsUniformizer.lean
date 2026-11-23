import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.Div.IdeleAtNorm

theorem absE_ideleAt_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (ϖ : (Fv F v)ˣ)
    (e : (Fv F v ⊗[F] E)ˣ), splitProj t (e : Fv F v ⊗[F] E) = ϖ → splitProj (t.comp σ) (e : Fv F v ⊗[F] E) = 1 →
    (GlobalTheory.Doubling.absE F E (GlobalTheory.Doubling.ideleAt F E v e) : ℝ) = nabs (Fv F v) ϖ := by
  intro F E _ _ _ _ _ σ hcm v t ϖ e h1 h2
  have key : Algebra.norm (Fv F v) (e : Fv F v ⊗[F] E) = ϖ := by
    have h := congrArg (splitProj t) (GlobalTheory.Doubling.algebraMap_norm_eq hcm (e : Fv F v ⊗[F] E))
    rw [AlgHom.commutes, map_mul, ← splitProj_comp, h1, h2, mul_one] at h
    simpa using h
  rw [GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_apply]
  have := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 ϖ).1
  simp only [coe_nnnorm]
  rw [key]
  exact this

end GlobalTheory.Div.IdeleAtNorm
