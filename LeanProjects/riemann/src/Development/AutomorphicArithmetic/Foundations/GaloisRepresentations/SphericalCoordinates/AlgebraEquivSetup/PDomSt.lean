import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private noncomputable def UpperTheory.Gal.W2.Seed.pDomSt_dL {I : Type} (a : I → ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun z k := a k * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' r z := by funext k; simp [mul_left_comm]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_theta_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) {n : ℕ}
    (Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ))
    (hΘ : ∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E))
    (b : 𝓞 E) (M : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E))
    (hM : ∀ x : Fin n → 𝓞 E, M (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) (x : ℝ ⊗[ℤ] (Fin n → 𝓞 E)) (k : Phi A × Fin n) :
    Θ (M x) k = k.1.1 (b : E) * Θ x k := by
  obtain ⟨τ, i⟩ := k
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    have h : r ⊗ₜ[ℤ] y = r • ((1 : ℝ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, LinearMap.map_smul, hM, LinearEquiv.map_smul, LinearEquiv.map_smul, Pi.smul_apply, Pi.smul_apply,
      hΘ, hΘ, Complex.real_smul, Complex.real_smul]
    simp [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb, mul_add]

private theorem UpperTheory.Gal.W2.Seed.pDomSt_term (D H z : ℂ) (e : ℝ) (hD : D.re = 0) (hH : H.im = 0) :
    (D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z).re = -D.im * H.re * e * Complex.normSq z := by
  have hD' : D = (D.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hD]
  have hH' : H = (H.re : ℂ) := by
    apply Complex.ext <;> simp [hH]
  have h1 : D * H * ((e : ℂ) * Complex.I * z) * (starRingEnd ℂ) z
      = D * H * e * Complex.I * (z * (starRingEnd ℂ) z) := by ring
  rw [h1, Complex.mul_conj, hD', hH']
  have h2 : (D.im : ℂ) * Complex.I * (H.re : ℂ) * (e : ℂ) * Complex.I * (Complex.normSq z : ℂ)
      = ((-D.im * H.re * e * Complex.normSq z : ℝ) : ℂ) := by
    push_cast
    linear_combination ((D.im : ℂ) * H.re * e * Complex.normSq z) * Complex.I_sq
  rw [h2, Complex.ofReal_re]
  simp

private theorem UpperTheory.Gal.W2.Seed.pDomSt_sum {I : Type} [Fintype I] [DecidableEq I] (k0 : I) (y : I → ℝ) :
    ∑ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * y k0 - ∑ k, y k := by
  have h : ∀ k, (if k = k0 then (1 : ℝ) else -1) * y k = 2 * (if k = k0 then y k else 0) - y k := by
    intro k
    split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem UpperTheory.Gal.W2.Seed.pDomSt :
    TraceType → RealIso → FormCoord → HdSign → DiagTrace → DomSt := by
  intro hT hR hF hS hD E _ _ _ A n hn
  classical
  obtain ⟨Θ, hΘ⟩ := hR E A n
  obtain ⟨-, hsum, -, him⟩ := hT E A
  let k0 : Phi A × Fin n := (⟨A.τ₀, rfl⟩, ⟨0, hn⟩)
  have hk0 : ∀ k : Phi A × Fin n,
      (InfinitePlace.mk k.1.1 = InfinitePlace.mk A.τ₀ ∧ (k.2 : ℕ) = 0) ↔ k = k0 := by
    rintro ⟨⟨τ, hτ⟩, i⟩
    constructor
    · rintro ⟨h1, h2⟩
      rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
      · exact Prod.ext (Subtype.ext h) (Fin.ext h2)
      · exfalso
        apply him
        have h3 : A.τ₀ (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) := by
          rw [← h, ComplexEmbedding.conjugate_coe_eq]
        rw [hτ] at h3
        exact Complex.conj_eq_iff_im.mp h3.symm
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  let ε : Phi A × Fin n → ℝ := fun k => if k = k0 then 1 else -1
  let a : Phi A × Fin n → ℂ := fun k => (ε k : ℂ) * Complex.I
  have ha2 : ∀ k, a k * a k = -1 := by
    intro k
    have h' : (ε k : ℂ) * (ε k) = 1 := by
      simp only [ε]
      split_ifs <;> norm_num
    simp only [a]
    linear_combination Complex.I ^ 2 * h' + Complex.I_sq
  have hca : ∀ k, (starRingEnd ℂ) (a k) = -a k := by
    intro k
    simp only [a, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  let J := Θ.symm.toLinearMap ∘ₗ pDomSt_dL a ∘ₗ Θ.toLinearMap
  have hJ : ∀ x k, Θ (J x) k = a k * Θ x k := by
    intro x k
    simp [J, pDomSt_dL]
  have hpos : ∀ k : Phi A × Fin n, 0 < -(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k) := by
    intro k
    have h1 := A.δ_sign k.1.1 k.1.2
    obtain ⟨-, -, hp, hm⟩ := hS E A n k.1.1 k.2
    have h2 : 0 < (k.1.1 (A.hd n k.2 : E)).re * ε k := by
      by_cases hk : k = k0
      · have := hp ((hk0 k).mpr hk)
        rw [show ε k = 1 from if_pos hk, mul_one]
        exact this
      · have := hm (fun h => hk ((hk0 k).mp h))
        rw [show ε k = -1 from if_neg hk, mul_neg_one]
        linarith
    exact mul_pos (by linarith) h2
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Θ.injective
    funext k
    rw [hJ, hJ, map_neg, Pi.neg_apply, ← mul_assoc, ha2]
    ring
  · intro x y
    rw [hF E A n Θ hΘ, hF E A n Θ hΘ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hJ, hJ, map_mul, hca]
    congr 2
    linear_combination (-(k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ x k * (starRingEnd ℂ) (Θ y k))) * ha2 k
  · intro x hx
    rw [hF E A n Θ hΘ]
    have hx' : Θ x ≠ 0 := by simpa using hx
    obtain ⟨k1, hk1⟩ : ∃ k, Θ x k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx' (funext h)
    have hterm : ∀ k : Phi A × Fin n,
        2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ (J x) k * (starRingEnd ℂ) (Θ x k)).re
          = 2 * ((-(k.1.1 A.δ).im * ((k.1.1 (A.hd n k.2 : E)).re * ε k)) * Complex.normSq (Θ x k)) := by
      intro k
      obtain ⟨hH, hD0, -, -⟩ := hS E A n k.1.1 k.2
      rw [hJ]
      simp only [a]
      rw [pDomSt_term _ _ _ _ hD0 hH]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (by norm_num) (mul_nonneg (hpos k).le (Complex.normSq_nonneg _))
    · exact ⟨k1, Finset.mem_univ _, mul_pos (by norm_num) (mul_pos (hpos k1) (Complex.normSq_pos.mpr hk1))⟩
  · intro b M hM
    apply LinearMap.ext
    intro x
    apply Θ.injective
    funext k
    simp only [LinearMap.comp_apply]
    rw [hJ, pDomSt_theta_mul A Θ hΘ b M hM, pDomSt_theta_mul A Θ hΘ b M hM, hJ]
    ring
  · intro c M hM
    dsimp only
    have htrM : LinearMap.trace ℝ _ M = 2 * (∑ k : Phi A × Fin n, k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' M Θ]
      refine hD _ (fun k : Phi A × Fin n => k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, pDomSt_theta_mul A Θ hΘ c M hM, LinearEquiv.apply_symm_apply]
    have htrJM : LinearMap.trace ℝ _ (J ∘ₗ M) = 2 * (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re := by
      rw [← LinearMap.trace_conj' (J ∘ₗ M) Θ]
      refine hD _ (fun k : Phi A × Fin n => a k * k.1.1 (c : E)) _ (fun z k => ?_)
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ, pDomSt_theta_mul A Θ hΘ c M hM,
        LinearEquiv.apply_symm_apply]
      ring
    have hre : (∑ k : Phi A × Fin n, a k * k.1.1 (c : E)).re = -∑ k, ε k * (k.1.1 (c : E)).im := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [a, Complex.mul_re]
    rw [hsum (fun τ => (n : ℂ) * τ (c : E))]
    constructor
    · rw [htrM]
      simp [ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.re_sum, Finset.mul_sum]
    · rw [htrJM, hre, pDomSt_sum k0 (fun k => (k.1.1 (c : E)).im)]
      simp [k0, ComplexEmbedding.conjugate_coe_eq, Fintype.sum_prod_type, Complex.im_sum, Finset.mul_sum]
      ring
