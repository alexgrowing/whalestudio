import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

namespace SplitSurj

theorem dbl_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem dbl_skew {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = -J i j) :
    ∀ i j, σ (dbl J j i) = -dbl J i j := by
  rintro (i | i) (j | j) <;> simp [dbl, hJ]

theorem isUnit_det_dbl_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    (t : E →ₐ[F] K) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : J.det ≠ 0) : IsUnit ((dbl J).map t).det := by
  have h1 : (J.map t).det ≠ 0 := by
    rw [show J.map t = (t : E →+* K).mapMatrix J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ
  rw [dbl, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.det_fromBlocks_zero₂₁]
  refine isUnit_iff_ne_zero.2 (mul_ne_zero h1 ?_)
  rw [show ((-J).map t) = -(J.map t) by ext i j; simp, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1

end SplitSurj

open SplitSurj in
theorem locMatD_surjOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 → (∀ i j, σ (J j i) = -J i j) →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.SurjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) Set.univ := by
  intro F E _ _ _ _ _ σ h d J hdet hJ v t c A _
  have hK := isUnit_det_dbl_map t J hdet
  have skew := dbl_skew σ J hJ
  let A' : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c * A * (dsum c)⁻¹
  let G : GL (Fin d ⊕ Fin d) (AE F E) := GlobalTheory.LeviIdx.adelicGL h t (dbl J) hK A'
  have hu : G ∈ UG (cA σ) (dbl (incM F J)) := by
    show (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl_incM]
    exact GlobalTheory.LeviIdx.adelicGL_unitary h t (dbl J) hK skew A'
  refine ⟨⟨G, hu⟩, GlobalTheory.LeviIdx.adelicGL_at h t (dbl J) hK A', ?_⟩
  change (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) G * dsum c = A
  rw [GlobalTheory.LeviIdx.adelicGL_map_piW]
  show (dsum c)⁻¹ * (dsum c * A * (dsum c)⁻¹) * dsum c = A
  group

end GlobalTheory.DblScal

end
