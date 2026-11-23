import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpSumCoeffEqZeroOfVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneThetaEmbeddingExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfThetaSumsTranslatesVanishStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKExpandXNz

open GlobalTheory.RealFreq Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symp_freq_left (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (w : Fin d → E) (y x : Fin n → E) (hyx : form σ JX y x = 1) {N : ℕ} (q : Fin N → Fin d → E) (t : Fin N → ℝ) :
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
  simp only [hTensR, LinearMap.coe_mk, AddHom.coe_mk, hTens_rat, hyx, map_neg, mul_neg,
    Finset.sum_neg_distrib, neg_mul, one_mul, map_sum, map_smul, smul_eq_mul]

omit [NumberField F] [NumberField E] in
theorem form_swap_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {d : ℕ} (J : Matrix (Fin d) (Fin d) E)
    (hherm : ∀ i j, σ (J j i) = J i j) (x y : Fin d → E) : form σ J y x = σ (form σ J x y) := by
  unfold form
  simp only [dotProduct, mulVec, map_sum, map_mul, hσ, hherm, Finset.mul_sum]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring)

theorem injective_real_frequencies (σ : E →ₐ[F] E) (B : Base F E)
    {n n₁ d : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d) (M : Model σ X W) (H : Plane E n n₁) (j₀ j₁ : ℕ)
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hB : B.IsGood σ) (hsig : ∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') :
    ∃ (N : ℕ) (emb : (Fin N → ℝ) → (Fin d → AE F E)) (lam : (Fin d → E) → Fin N → ℝ), Function.Injective lam ∧
      ∀ (w : Fin d → E) (t : Fin N → ℝ),
        B.ψ ((M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (incV F H.x) (emb t))).2 -
          (M.co.e (Matrix.vecMulVec (incV F H.x) (emb t))).1 ⬝ᵥ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))).2) =
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam w j : ℂ) * (t j : ℂ)) := by
  obtain ⟨r, s, r', s', hX, hW⟩ := hsig
  have hcm := hB.cm
  have hne : Nonempty (NumberField.InfinitePlace F) := inferInstance
  obtain ⟨v⟩ := hne
  have hσ : ∀ z : E, σ (σ z) = z := by
    intro z
    apply (B.emb v).1.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hyx : form σ X.J H.y H.x = 1 := by
    rw [form_swap_herm σ hσ X.J hX.herm, hH.xy, map_one]
  have hdet : W.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_sig _ r' s' (hW.sig v)
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  let b := Module.finBasis ℚ (Fin d → E)
  refine ⟨Module.finrank ℚ (Fin d → E), fun t => ∑ j, realAd F (t j) • incV F (b j),
    fun ξ j => -(realTr F (-form σ W.J ξ (b j))), ?_, ?_⟩
  · intro ξ ξ' hξ
    by_contra hne
    have hz : ∀ j, realTr F (form σ W.J (ξ - ξ') (b j)) = 0 := by
      intro j
      have := congrFun hξ j
      simp only [map_neg, neg_inj] at this
      rw [form, sub_dotProduct, map_sub]
      unfold form at this
      rw [this, sub_self]
    let L : (Fin d → E) →+ ℝ := (realTr F).comp
      { toFun := form σ W.J (ξ - ξ')
        map_zero' := by
          unfold form
          rw [show (fun i => σ ((0 : Fin d → E) i)) = 0 from funext fun i => map_zero σ, Matrix.mulVec_zero,
            dotProduct_zero]
        map_add' := fun u v => by
          unfold form
          rw [show (fun i => σ ((u + v) i)) = (fun i => σ (u i)) + (fun i => σ (v i)) from funext fun i => map_add σ _ _,
            Matrix.mulVec_add, dotProduct_add] }
    have hL : L.toRatLinearMap = 0 := b.ext fun j => hz j
    have hw : (ξ - ξ') ᵥ* W.J ≠ 0 := by
      intro h0
      apply hne
      have := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet))
        (h0.trans (Matrix.zero_vecMul _).symm)
      exact sub_eq_zero.1 this
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hw
    have h1 : form σ W.J (ξ - ξ') (Pi.single k (σ ((((ξ - ξ') ᵥ* W.J) k)⁻¹))) = 1 := by
      rw [form_single, hσ]
      exact mul_inv_cancel₀ hk
    have h2 := LinearMap.congr_fun hL (Pi.single k (σ ((((ξ - ξ') ᵥ* W.J) k)⁻¹)))
    change realTr F (form σ W.J (ξ - ξ') _) = 0 at h2
    rw [h1] at h2
    exact realTr_one_ne hcm.2.2.1 h2
  · intro ξ t
    rw [← M.co.form, symp_freq_left σ X.J W.J ξ H.y H.x hyx b t, psi_freq B.ψ hB.std]
    congr 1
    simp only [realTr_apply]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.ThKExpandXNz

namespace GlobalTheory.ThKExpandXNz

open GlobalTheory.ThetaQuasiRat

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∃ φ ∈ schA F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (φ)))) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M hM n₁ X₁ H j₀ j₁ M₂ hH hM₂ e₀ he hB hXW
  have hstd : IsStd B.ψ := hB.std
  have hρ : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) := fun w Φ hΦ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hstd _ _ Φ hΦ
  have hth : ∀ (c : ℂ) (φ : Fn F n₁ d), thetaSum F (c • φ) = c * thetaSum F φ := fun c φ => by
    simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

  have hswap : ∀ (a b : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : Fn F n d),
      schr B.ψ a (schr B.ψ b φ) = B.ψ (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) • schr B.ψ b (schr B.ψ a φ) := by
    intro a b φ
    rw [schr_schr, schr_schr, add_comm b a, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
    linear_combination (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) * h2
  by_contra hcon
  push_neg at hcon

  have hA : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ w : Fin d → E,
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)) = 0 := by
    intro Ψ hΨ
    obtain ⟨N, emb, lam, hinj, hexp⟩ := injective_real_frequencies σ B X X₁ W M H j₀ j₁ hH hB hXW
    refine GlobalTheory.T.exp_sum_coeff_eq_zero_of_vanishing N (Fin d → E) lam _ hinj
      (GlobalTheory.T.adapted_mixed_model_evaluation hKP F E σ B n d X W M hM n₁ X₁ H j₀ j₁ M₂ hH hM₂ e₀ he hB hXW Ψ hΨ) ?_
    intro t
    have h0 := hcon _ (hρ (Matrix.vecMulVec (incV F H.x) (emb t)) Ψ hΨ)
    rw [← h0]
    refine tsum_congr fun w => ?_
    have hinv := he.inv (Matrix.vecMulVec (incV F H.x) (emb t)) ⟨emb t, rfl⟩ _
      (hρ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ hΨ)
    simp only [Darboux.rho] at hinv ⊢
    rw [hswap, LinearMap.map_smul, hinv, hth, hexp, mul_comm]

  have hB0 : ∀ Ψ ∈ schA F (Fin n × Fin d), thetaSum F (e₀ Ψ) = 0 := by
    intro Ψ hΨ
    have h := hA Ψ hΨ 0
    have h1 : Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E)) = 0 := by
      ext i j
      simp [incV, Matrix.vecMulVec_apply]
    have h2 : M.co.rho B.ψ 0 Ψ = Ψ := by
      funext x
      simp [Darboux.rho, schr]
    rwa [h1, h2] at h

  have hC : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ x y : Fin n₁ × Fin d → AF F, thetaSum F (schr B.ψ (x, y) (e₀ Ψ)) = 0 := by
    intro Ψ hΨ x y
    have h := he.Heisenberg₂ (M₂.co.e.symm (x, y)) Ψ hΨ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply] at h
    rw [← h]
    exact hB0 _ (hρ _ Ψ hΨ)
  obtain ⟨Ψ, hΨ, hne⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n₁ d X W X₁ W M M₂ H.ι 1 _ e₀ hM hM₂ he
  exact hne (GlobalTheory.T.eq_zero_of_theta_sums_translates_vanish F B.ψ hstd _ (e₀ Ψ) (he.maps Ψ hΨ) (hC Ψ hΨ))

end GlobalTheory.ThKExpandXNz

end
