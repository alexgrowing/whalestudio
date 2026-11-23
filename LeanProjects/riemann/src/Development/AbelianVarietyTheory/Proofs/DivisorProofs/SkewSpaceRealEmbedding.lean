import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneThetaEmbeddingExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.RealFreqSnd
open Matrix GlobalTheory.RealFreq

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symp_freq_snd (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (y x : Fin n → E) (hyx : form σ JX y x = 1) (w : Fin d → E) {N : ℕ} (q : Fin N → Fin d → E) (t : Fin N → ℝ) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (vecMulVec (incV F y) (incV F w))
      (vecMulVec (incV F x) (∑ j, realAd F (t j) • incV F (q j))) =
      ∑ j, realAd F (t j) * Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (-form σ JW w (q j))) := by
  have hv : vecMulVec (incV F x) (∑ j, realAd F (t j) • incV F (q j)) =
      ∑ j, realAd F (t j) • vecMulVec (incV F x) (incV F (q j)) := by
    ext i l
    simp [vecMulVec_apply, Matrix.sum_apply, Finset.mul_sum, mul_smul_comm]
  unfold symp
  rw [hv]
  change Algebra.trace (AF F) (AE F E) (-1 * hTensR σ (incM F JX) (incM F JW) _ (∑ j, _)) = _
  rw [map_sum]
  simp only [map_smul]
  simp only [hTensR, LinearMap.coe_mk, AddHom.coe_mk, hTens_rat, hyx, map_neg,
    Finset.sum_neg_distrib, neg_mul, mul_neg, one_mul, map_sum, map_smul, smul_eq_mul]

omit [NumberField F] [NumberField E] in
theorem form_swap_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {d : ℕ} (J : Matrix (Fin d) (Fin d) E)
    (hherm : ∀ i j, σ (J j i) = J i j) (x y : Fin d → E) : form σ J y x = σ (form σ J x y) := by
  unfold form
  simp only [dotProduct, mulVec, map_sum, map_mul, hσ, hherm, Finset.mul_sum]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring)

theorem injective_realTr_form (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (h2 : Module.finrank F E = 2) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hdet : J.det ≠ 0) {ι : Type} (b : Module.Basis ι ℚ (Fin n → E)) :
    Function.Injective fun (ξ : Fin n → E) (j : ι) => realTr F (form σ J ξ (b j)) := by
  intro ξ ξ' hξ
  by_contra hne
  have hz : ∀ j, realTr F (form σ J (ξ - ξ') (b j)) = 0 := by
    intro j
    have := congrFun hξ j
    rw [form, sub_dotProduct, map_sub]
    unfold form at this
    simp only at this
    rw [this, sub_self]
  let L : (Fin n → E) →+ ℝ := (realTr F).comp
    { toFun := form σ J (ξ - ξ')
      map_zero' := by
        unfold form
        rw [show (fun i => σ ((0 : Fin n → E) i)) = 0 from funext fun i => map_zero σ, Matrix.mulVec_zero,
          dotProduct_zero]
      map_add' := fun u v => by
        unfold form
        rw [show (fun i => σ ((u + v) i)) = (fun i => σ (u i)) + (fun i => σ (v i)) from funext fun i => map_add σ _ _,
          Matrix.mulVec_add, dotProduct_add] }
  have hL : L.toRatLinearMap = 0 := b.ext fun j => hz j
  have hw : (ξ - ξ') ᵥ* J ≠ 0 := by
    intro h0
    apply hne
    have := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet))
      (h0.trans (Matrix.zero_vecMul _).symm)
    exact sub_eq_zero.1 this
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hw
  have h1 : form σ J (ξ - ξ') (Pi.single k (σ ((((ξ - ξ') ᵥ* J) k)⁻¹))) = 1 := by
    rw [form_single, hσ]
    exact mul_inv_cancel₀ hk
  have h3 := LinearMap.congr_fun hL (Pi.single k (σ ((((ξ - ξ') ᵥ* J) k)⁻¹)))
  change realTr F (form σ J (ξ - ξ') _) = 0 at h3
  rw [h1] at h3
  exact realTr_one_ne h2 h3

end

theorem injective_real_frequencies_snd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ x y : Fin n → E, form σ X.J x y = 1 →
    ∃ (N : ℕ) (emb : (Fin N → ℝ) → (Fin d → AE F E)) (lam : (Fin d → E) → Fin N → ℝ), Function.Injective lam ∧
      ∀ (w : Fin d → E) (t : Fin N → ℝ),
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F y) (incV F w))
            (Matrix.vecMulVec (incV F x) (emb t))) =
          Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam w j : ℂ) * (t j : ℂ)) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW x y hxy
  have hcm := hB.cm
  have hne : Nonempty (NumberField.InfinitePlace F) := inferInstance
  obtain ⟨v⟩ := hne
  have hσ : ∀ z : E, σ (σ z) = z := by
    intro z
    apply (B.emb v).1.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hyx : form σ X.J y x = 1 := by
    rw [form_swap_herm σ hσ X.J hX.herm, hxy, map_one]
  have hdet : W.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_sig _ r' s' (hW.sig v)
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  let b := Module.finBasis ℚ (Fin d → E)
  refine ⟨Module.finrank ℚ (Fin d → E), fun t => ∑ j, realAd F (t j) • incV F (b j),
    fun w j => realTr F (form σ W.J w (b j)), injective_realTr_form σ hσ hcm.2.2.1 W.J hdet b, ?_⟩
  intro w t
  rw [symp_freq_snd σ X.J W.J y x hyx w b t, psi_freq B.ψ hB.std]
  congr 1
  simp only [← realTr_apply]
  simp only [map_neg]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.RealFreqSnd
