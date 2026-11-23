import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : A'ᵀ * M * A'.map star =
      Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)) := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul] at hdet
  have : (1 : Matrix (Fin r) (Fin r) ℂ).det * (-1 : Matrix (Fin s) (Fin s) ℂ).det ≠ 0 := by
    rw [Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  exact this hdet.symm

theorem incM_mulVec_cA_surjective (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n r s : ℕ) (X : Spc F E n) :
    B.IsGood σ → X.IsHerm σ B r s → ∀ z : Fin n → AE F E, ∃ y : Fin n → AE F E,
      (incM F X.J *ᵥ fun k => cA σ (y k)) = z := by
  intro hB hX z

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hM := det_ne_zero_of_hasSig (hX.sig w)
  have hJ : X.J.det ≠ 0 := by
    intro h0
    apply hM
    have := RingHom.map_det ((B.emb w).1) X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hU : IsUnit (incM F X.J).det := by
    have := RingHom.map_det (inclR (F := F) (E := E) (AF F)) X.J
    unfold incM
    rw [show X.J.map (inclR (AF F)) = (inclR (F := F) (E := E) (AF F)).mapMatrix X.J from rfl, ← this]
    exact (isUnit_iff_ne_zero.mpr hJ).map _

  have hfin : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hσs : Function.Surjective σ :=
    (LinearMap.injective_iff_surjective (f := σ.toLinearMap)).mp σ.toRingHom.injective
  have hcs : Function.Surjective (cA σ) :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) hσs
  choose g hg using hcs
  refine ⟨fun k => g (((incM F X.J)⁻¹ *ᵥ z) k), ?_⟩
  simp only [hg]
  show incM F X.J *ᵥ ((incM F X.J)⁻¹ *ᵥ z) = z
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]

end GlobalTheory.ThK
