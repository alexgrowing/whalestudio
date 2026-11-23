import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NilLift

variable {n : ℕ}

theorem hs_eq_trace (M : Matrix (Fin n) (Fin n) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_nonneg' (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs M := by
  simp only [Formalism.REAL.hs]
  positivity

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ (∀ u, P *ᵥ u ∈ W) ∧ ∀ u ∈ W, P *ᵥ u = u := by
  classical
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    W.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := K.starProjection
  have hT : ∀ u, (Matrix.toEuclideanLin.symm T) *ᵥ u = WithLp.ofLp (T (WithLp.toLp 2 u)) := by
    intro u
    have h := congrArg (fun f : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) =>
      WithLp.ofLp (f (WithLp.toLp 2 u))) (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin T)
    exact h
  refine ⟨Matrix.toEuclideanLin.symm T, ?_, ?_, ?_⟩
  · have hH : (Matrix.toEuclideanLin.symm T).IsHermitian := by
      rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearEquiv.apply_symm_apply]
      exact K.starProjection_isSymmetric
    exact hH
  · intro u
    rw [hT]
    have hm : T (WithLp.toLp 2 u) ∈ K := K.starProjection_apply_mem _
    exact hm
  · intro u hu
    rw [hT]
    have hm : WithLp.toLp 2 u ∈ K := hu
    have h2 : T (WithLp.toLp 2 u) = WithLp.toLp 2 u := K.starProjection_eq_self_iff.mpr hm
    rw [h2]

theorem hs_mul_le (D Q : Matrix (Fin n) (Fin n) ℂ) (h1 : Qᴴ = Q) (h2 : Q * Q = Q) :
    hs (D * (1 - Q)) ≤ hs D := by
  have hR : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, h2, sub_self, sub_zero]
  have hDQ : hs (D * Q) = (trace (D * Q * Dᴴ)).re := by
    rw [hs_eq_trace, Matrix.trace_mul_comm, Matrix.conjTranspose_mul, h1, mul_assoc,
      ← mul_assoc Q Q, h2, ← mul_assoc]
  have hDR : hs (D * (1 - Q)) = (trace (D * Dᴴ)).re - (trace (D * Q * Dᴴ)).re := by
    rw [hs_eq_trace, Matrix.trace_mul_comm, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, h1, mul_assoc, ← mul_assoc (1 - Q) (1 - Q), hR, ← mul_assoc,
      mul_sub, mul_one, sub_mul, Matrix.trace_sub, Complex.sub_re]
  have hD : hs D = (trace (D * Dᴴ)).re := by rw [hs_eq_trace, Matrix.trace_mul_comm]
  have h0 := hs_nonneg' (D * Q)
  linarith

theorem core (J P D : Matrix (Fin n) (Fin n) ℂ) (j1 : J * J = 1) (j2 : Jᴴ = J) (p1 : Pᴴ = P)
    (p2 : P * P = P) (p3 : P * J * P = 0) (d1 : D * P = 0)
    (d2 : P * (D * (1 - J * P * J)) = D * (1 - J * P * J)) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ * J + J * A = 0 ∧ P * J * A = 0 ∧
      (∀ u, (P * J) *ᵥ u = 0 → A *ᵥ u = D *ᵥ u) ∧ hs A ≤ 2 * hs D := by
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← mul_assoc, j1, one_mul]
  have hPP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (P * X) = P * X := fun X => by
    rw [← mul_assoc, p2]
  have hPJP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (J * (P * X)) = 0 := fun X => by
    rw [← mul_assoc, ← mul_assoc, p3, zero_mul]
  have hPDh : P * Dᴴ = 0 := by
    have h := congrArg conjTranspose d1
    rwa [conjTranspose_mul, p1, conjTranspose_zero] at h
  obtain ⟨B, hB⟩ : ∃ B, B = D * (1 - J * P * J) := ⟨_, rfl⟩
  rw [← hB] at d2
  have hBJP : B * (J * P) = 0 := by
    rw [hB]
    simp only [mul_assoc, sub_mul, mul_sub, one_mul, mul_one, hJJ, p2, hPP, sub_self, mul_zero]
  have hBJB : B * (J * B) = 0 := by
    calc B * (J * B) = B * (J * (P * B)) := by rw [d2]
      _ = B * (J * P) * B := by simp only [mul_assoc]
      _ = 0 := by rw [hBJP, zero_mul]
  have hBhP : Bᴴ * P = Bᴴ := by
    have h := congrArg conjTranspose d2
    rwa [conjTranspose_mul, p1] at h
  have hPBh : P * Bᴴ = 0 := by
    rw [hB]
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, j2, p1, mul_sub, sub_mul,
      one_mul, mul_one, mul_assoc, hPJP, hPDh, sub_zero, sub_self]
  have hPBhX : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (Bᴴ * X) = 0 := fun X => by
    rw [← mul_assoc, hPBh, zero_mul]
  have hPJB : P * (J * B) = 0 := by
    calc P * (J * B) = P * (J * (P * B)) := by rw [d2]
      _ = 0 := hPJP B
  have hBhJBh : ∀ X : Matrix (Fin n) (Fin n) ℂ, Bᴴ * (J * (Bᴴ * X)) = 0 := by
    intro X
    have h := congrArg conjTranspose hBJB
    rw [conjTranspose_mul, conjTranspose_mul, j2, conjTranspose_zero] at h
    rw [← mul_assoc, ← mul_assoc, h, zero_mul]
  refine ⟨B - J * Bᴴ * J, ?_, ?_, ?_, ?_⟩
  · simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, j2, sub_mul,
      mul_sub, mul_assoc, j1, hJJ, mul_one]
    abel
  · simp only [mul_sub, mul_assoc, hJJ, hPJB, hPBhX, sub_self]
  · intro u hu
    have e1 : J * Bᴴ * J = J * Bᴴ * (P * J) := by
      conv_lhs => rw [← hBhP]
      simp only [mul_assoc]
    have e2 : B = D - D * J * (P * J) := by
      rw [hB, mul_sub, mul_one]
      simp only [mul_assoc]
    have hA : B - J * Bᴴ * J = D - (D * J + J * Bᴴ) * (P * J) := by
      rw [e1, add_mul, ← sub_sub, ← e2]
    rw [hA, sub_mulVec, ← mulVec_mulVec, hu, mulVec_zero, sub_zero]
  · have hK1 : (J * P * J)ᴴ = J * P * J := by
      simp only [conjTranspose_mul, j2, p1, mul_assoc]
    have hK2 : J * P * J * (J * P * J) = J * P * J := by
      simp only [mul_assoc, hJJ, hPP]
    have hsB : hs B ≤ hs D := by
      rw [hB]
      exact hs_mul_le D (J * P * J) hK1 hK2
    have hM : (B - J * Bᴴ * J)ᴴ * (B - J * Bᴴ * J) = Bᴴ * B + J * (B * (Bᴴ * J)) := by
      simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, j2, sub_mul,
        mul_sub, mul_assoc, hJJ, hBJB, hBhJBh, mul_zero, sub_zero, zero_sub, sub_neg_eq_add]
    have t1 : trace (J * (B * (Bᴴ * J))) = trace (Bᴴ * B) := by
      rw [Matrix.trace_mul_comm, mul_assoc, mul_assoc, j1, mul_one, Matrix.trace_mul_comm]
    have hsA : hs (B - J * Bᴴ * J) = 2 * hs B := by
      rw [hs_eq_trace, hs_eq_trace, hM, Matrix.trace_add, t1, Complex.add_re]
      ring
    rw [hsA]
    linarith

theorem hform_eq (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) H x y = star x ⬝ᵥ (H *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]

theorem hform_mulVec (H X Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) H (X *ᵥ x) (Y *ᵥ y) = star x ⬝ᵥ ((Xᴴ * H * Y) *ᵥ y) := by
  rw [hform_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem ext_mulVec' {X Y : Matrix (Fin n) (Fin n) ℂ} (h : ∀ u, X *ᵥ u = Y *ᵥ u) : X = Y := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h1

private theorem jm_sq_lemma (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem jm_herm_lemma_2 (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem exists_lift : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  intro n ε H G D W hG hJ hiso hDW hDperp
  classical
  have j1 : Jm ε * Jm ε = 1 := jm_sq_lemma ε
  have j2 : (Jm ε)ᴴ = Jm ε := jm_herm_lemma_2 ε
  have hGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hiGX : ∀ X : Matrix (Fin n) (Fin n) ℂ, G⁻¹ * (G * X) = X := fun X => by
    rw [← mul_assoc, hiG, one_mul]
  have hGu : ∀ u : Fin n → ℂ, G *ᵥ (G⁻¹ *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hGi, one_mulVec]
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← mul_assoc, j1, one_mul]
  obtain ⟨P, p1, hPW, hPfix⟩ := exists_proj (W.comap (Matrix.toLin' G))
  have hPW' : ∀ u, G *ᵥ (P *ᵥ u) ∈ W := fun u => by
    have h := hPW u
    rwa [Submodule.mem_comap, Matrix.toLin'_apply] at h
  have hPfix' : ∀ v, G *ᵥ v ∈ W → P *ᵥ v = v := fun v hv =>
    hPfix v (by rwa [Submodule.mem_comap, Matrix.toLin'_apply])
  have p2 : P * P = P := ext_mulVec' fun u => by
    rw [← mulVec_mulVec]
    exact hPfix' _ (hPW' u)
  have hPP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (P * X) = P * X := fun X => by
    rw [← mul_assoc, p2]
  have hf : ∀ a b : Fin n → ℂ,
      Formalism.UG.hform (starRingEnd ℂ) H (G *ᵥ a) (G *ᵥ b) = star a ⬝ᵥ (Jm ε *ᵥ b) := fun a b => by
    rw [hform_mulVec, hJ]
  have hPs : ∀ a z : Fin n → ℂ, star (P *ᵥ a) ⬝ᵥ z = star a ⬝ᵥ (P *ᵥ z) := fun a z => by
    rw [star_mulVec, ← dotProduct_mulVec, p1]
  have hperp : ∀ v, G *ᵥ v ∈ perpSet (starRingEnd ℂ) H W ↔ (P * Jm ε) *ᵥ v = 0 := by
    intro v
    simp only [perpSet, Set.mem_setOf_eq]
    constructor
    · intro h
      apply dotProduct_star_self_eq_zero.mp
      rw [← mulVec_mulVec, ← hPs, ← hf]
      exact h _ (hPW' _)
    · intro h w hw
      rw [← hGu w, hf, ← hPfix' (G⁻¹ *ᵥ w) (by rw [hGu]; exact hw), hPs, mulVec_mulVec, h,
        dotProduct_zero]
  have p3 : P * Jm ε * P = 0 := ext_mulVec' fun u => by
    rw [zero_mulVec, ← mulVec_mulVec]
    exact (hperp _).mp (hiso _ (hPW' u))
  have hDv : ∀ v, (G⁻¹ * D * G) *ᵥ v = G⁻¹ *ᵥ (D *ᵥ (G *ᵥ v)) := fun v => by
    simp only [← mulVec_mulVec]
  have d1 : G⁻¹ * D * G * P = 0 := ext_mulVec' fun u => by
    rw [zero_mulVec, ← mulVec_mulVec, hDv, hDW _ (hPW' u), mulVec_zero]
  have d2 : P * (G⁻¹ * D * G * (1 - Jm ε * P * Jm ε)) = G⁻¹ * D * G * (1 - Jm ε * P * Jm ε) :=
    ext_mulVec' fun u => by
      have hz : (P * Jm ε) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ u) = 0 := by
        rw [mulVec_mulVec, mul_sub, mul_one]
        simp only [mul_assoc, hJJ, hPP, sub_self, zero_mulVec]
      have hm : G *ᵥ ((G⁻¹ * D * G) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ u)) ∈ W := by
        rw [hDv, hGu]
        exact hDperp _ ((hperp _).mpr hz)
      rw [← mulVec_mulVec _ P, ← mulVec_mulVec _ (G⁻¹ * D * G)]
      exact hPfix' _ hm
  obtain ⟨A', hA1, hA2, hA3, hA4⟩ := core (Jm ε) P (G⁻¹ * D * G) j1 j2 p1 p2 p3 d1 d2
  have hAv : ∀ v, (G * A' * G⁻¹) *ᵥ (G *ᵥ v) = G *ᵥ (A' *ᵥ v) := fun v => by
    simp only [mulVec_mulVec, mul_assoc, hiG, mul_one]
  have hagree : ∀ u ∈ perpSet (starRingEnd ℂ) H W, (G * A' * G⁻¹) *ᵥ u = D *ᵥ u := by
    intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
    rw [hAv, hA3 v ((hperp v).mp hu), hDv, hGu]
  refine ⟨G * A' * G⁻¹, ?_, hagree, ?_⟩
  · unfold InNil IsSkew
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u u'
      obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
      obtain ⟨v', rfl⟩ : ∃ v', u' = G *ᵥ v' := ⟨G⁻¹ *ᵥ u', (hGu u').symm⟩
      rw [hAv, hAv, hf, hf, star_mulVec, ← dotProduct_mulVec, ← dotProduct_add, mulVec_mulVec,
        mulVec_mulVec, ← add_mulVec, hA1, zero_mulVec, dotProduct_zero]
    · intro u
      obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
      rw [hAv, hperp, mulVec_mulVec, hA2, zero_mulVec]
    · intro u hu
      rw [hagree u hu]
      exact hDperp u hu
    · intro u hu
      rw [hagree u (hiso u hu)]
      exact hDW u hu
  · have hc : G⁻¹ * (G * A' * G⁻¹) * G = A' := by
      simp only [mul_assoc, hiG, mul_one, hiGX]
    rw [hc]
    exact hA4

end GlobalTheory.NilLift
