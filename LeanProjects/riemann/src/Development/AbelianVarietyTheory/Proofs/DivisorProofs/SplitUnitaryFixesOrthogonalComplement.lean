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

namespace GlobalTheory.ConjFix

theorem conj_fix : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsHermND σ J → ∀ {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    (x : GLoc σ J v) (W : Submodule (Fv F v) (Fin n → Fv F v)), (∀ z, ((splitHom σ J τ x).1 - 1) *ᵥ z ∈ W) →
    ∀ (u : Fin n → Fv F v), (∀ w ∈ W, u ⬝ᵥ (J.map τ *ᵥ w) = 0) → (splitHom σ J (τ.comp σ) x).1 *ᵥ u = u := by
  intro F E _ _ _ _ σ n J hJ v τ x W hW u hu
  set M₁ := (splitHom σ J τ x).1 with hM₁
  set M₂ := (splitHom σ J (τ.comp σ) x).1 with hM₂
  have hpair : ∀ z, (M₂ *ᵥ u) ⬝ᵥ J.map τ *ᵥ (M₁ *ᵥ z) = u ⬝ᵥ J.map τ *ᵥ z :=
    fun z => pairing_splitHom τ x u z
  have hfix : ∀ z, u ⬝ᵥ J.map τ *ᵥ (M₁ *ᵥ z) = u ⬝ᵥ J.map τ *ᵥ z := by
    intro z
    have h0 := hu _ (hW z)
    have : M₁ *ᵥ z = z + (M₁ - 1) *ᵥ z := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [this, Matrix.mulVec_add, dotProduct_add, h0, add_zero]
  have h1 : ∀ z, (M₂ *ᵥ u - u) ⬝ᵥ J.map τ *ᵥ (M₁ *ᵥ z) = 0 := by
    intro z; rw [sub_dotProduct, hpair, hfix, sub_self]
  have h2 : ∀ w, (M₂ *ᵥ u - u) ⬝ᵥ J.map τ *ᵥ w = 0 := by
    intro w
    have hw : M₁ *ᵥ ((splitHom σ J τ x)⁻¹.1 *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, hM₁, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := h1 ((splitHom σ J τ x)⁻¹.1 *ᵥ w)
    rwa [hw] at this
  have h3 : Matrix.vecMul (M₂ *ᵥ u - u) (J.map τ) = 0 := by
    funext i
    have := h2 (Pi.single i 1)
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    simpa using this
  have h4 : M₂ *ᵥ u - u = 0 := by
    have hG : J.map τ * (splitGram hJ τ)⁻¹.1 = 1 := by
      rw [← splitGram_val hJ τ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc M₂ *ᵥ u - u = Matrix.vecMul (M₂ *ᵥ u - u) (J.map τ * (splitGram hJ τ)⁻¹.1) := by
          rw [hG, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h3, Matrix.zero_vecMul]
  exact sub_eq_zero.mp h4

end GlobalTheory.ConjFix
