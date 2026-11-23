import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermValue_inclR (v : Fin n → E) :
    hermValue F J F (fun i => inclR (F := F) F (v i)) =
      inclR (F := F) F (hE (conj F E).toAlgHom J v v) := by
  have hc : ∀ e : E, conjBase F E F (inclR (F := F) F e) = inclR (F := F) F (conj F E e) := fun e => rfl
  have hb : baseMatrix F J F = J.map (inclR (F := F) F) := rfl
  simp only [hermValue, hc, hb, hE, Formalism.UG.hform, dotProduct, mulVec, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply, mul_assoc]

theorem ofResVec_cvec (v : Fin n → E) :
    ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v) = fun i => inclR (F := F) F (v i) := by
  apply resVec_injective (ι := Fin n) (Module.finBasis F E) F
  rw [resVec_ofResVec]
  funext p
  simp only [cvec, resVec, Function.comp_apply, coordsVec, coords, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hermCoords_cvec_ne_zero {v : Fin n → E} (h : hE (conj F E).toAlgHom J v v ≠ 0) :
    hermCoords J (Module.finBasis F E) F (cvec F v) ≠ 0 := by
  intro h0
  apply h
  have h1 : hermValue F J F (ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v)) = 0 := by
    apply (coords (Module.finBasis F E) F).injective
    rw [map_zero]
    exact h0
  rw [ofResVec_cvec, hermValue_inclR] at h1
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective (h1.trans (map_zero _).symm)

theorem matHom_mem_unitaryPoints (g : GAd (conj F E).toAlgHom J) :
    matHom (AF F) (conj F E).toAlgHom J g ∈ unitaryPoints F E J (AF F) := by
  rw [← CompanionTheory.SWFin.HR_eq]
  exact g.2

theorem exists_pos_isotropic_of_hgt_lt :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd (conj F E).toAlgHom J) (v : Fin n → E), v ≠ 0 →
      hgt (conj F E).toAlgHom J g v < ε → hE (conj F E).toAlgHom J v v = 0 := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos
    (hermPoly J (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  refine ⟨min 1 C⁻¹, lt_min one_pos (inv_pos.2 hC), fun g v hv hlt => ?_⟩
  by_contra hne
  rw [hgt_eq] at hlt
  have hx : cvec F v ≠ 0 := cvec_ne_zero hv
  have hz := hermCoords_cvec_ne_zero J hne
  have hy := Reduction.hasFiniteContent_height (trG (conj F E).toAlgHom J g) hx
  have he : (fun k => MvPolynomial.aeval
      (Reduction.ratVec (cvec F v) ᵥ* ((trG (conj F E).toAlgHom J g : GL _ (AF F)) : Matrix _ _ (AF F)))
      (hermPoly J (Module.finBasis F E) k)) =
      Reduction.ratVec (hermCoords J (Module.finBasis F E) F (cvec F v)) := by
    funext k
    rw [aeval_hermPoly]
    exact congrFun (hermCoords_vecMul_trHom J (Module.finBasis F E) (cvec F v)
      ⟨_, matHom_mem_unitaryPoints J g⟩) k
  have hfz := Reduction.hasFiniteContent_ratVec hz
  rw [← he] at hfz
  have h1 := Reduction.one_le_adelicNorm_ratVec hz
  rw [← he] at h1
  have h2 : 1 ≤ C * Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v) ^ 2 :=
    h1.trans (hCb _ hy hfz)
  have h0 := Reduction.height_nonneg (trG (conj F E).toAlgHom J g) (cvec F v)
  set t := Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v)
  have ht1 : t < 1 := hlt.trans_le (min_le_left _ _)
  have htC : t < C⁻¹ := hlt.trans_le (min_le_right _ _)
  have h3 : C * t < 1 := by
    have := mul_lt_mul_of_pos_left htC hC
    rwa [mul_inv_cancel₀ hC.ne'] at this
  have h4 : C * t ^ 2 ≤ C * t := by
    nlinarith [mul_nonneg (mul_nonneg hC.le h0) (sub_nonneg.2 ht1.le)]
  linarith

end GlobalTheory.CompanionTheory.RedCov.Bridge

namespace GlobalTheory.CompanionTheory.RedCov

theorem isotropic_of_hgt_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  intro F E _ _ _ _ _ σ h n J _
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((h.2.2.2 τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  exact Bridge.exists_pos_isotropic_of_hgt_lt J

end GlobalTheory.CompanionTheory.RedCov

end
