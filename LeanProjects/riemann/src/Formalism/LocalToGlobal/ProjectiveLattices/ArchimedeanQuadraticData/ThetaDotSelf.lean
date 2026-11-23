import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.HQsmulRight
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinrankCmType

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

theorem trace_id (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ)
    (Q : ι → Matrix (Fin r) (Fin r) ℂ) (p : ℕ) (S : HermForm K r)
    (hform : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (y v : Fin r → K) :
    rho eqv (Theta p (Phi σ Q y)) ⬝ᵥ rho eqv (Phi σ Q v) =
      (1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h y v) : ℚ) : ℝ) := by
  rw [rho_dot, ← sum_re_cmType σ hinj hcm (S.h y v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hform i y v, jForm, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Theta, Phi, map_mul, sgn_conj]
  ring_nf

private lemma rho_dot_self_lemma {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ j, Complex.normSq (w i j) := by
  unfold rho
  simp only [dotProduct]
  refine (Equiv.sum_comp eqv (fun x : ι × Fin r × Fin 2 =>
    (if x.2.2 = 0 then (w x.1 x.2.1).re else (w x.1 x.2.1).im) *
      (if x.2.2 = 0 then (w x.1 x.2.1).re else (w x.1 x.2.1).im))).trans ?_
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]

theorem theta_dot_self (p : ℕ) {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv (Theta p w) ⬝ᵥ rho eqv (Theta p w) = rho eqv w ⬝ᵥ rho eqv w := by
  rw [rho_dot_self_lemma, rho_dot_self_lemma]
  unfold Theta sgn
  simp only [map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem phi_dot_self (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {N : ℕ}
    (eqv : Fin N ≃ ι × Fin r × Fin 2) (v : Fin r → K) :
    rho eqv (Phi σ Q v) ⬝ᵥ rho eqv (Phi σ Q v) = majSq σ Q v := by
  rw [rho_dot_self_lemma]
  unfold Phi majSq normSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.normSq_eq_norm_sq _

theorem trace_one_ne : Algebra.trace ℚ K 1 ≠ 0 := by
  rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap]
  simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
  exact Module.finrank_pos.ne'

theorem nondeg [Nonempty ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (hQ : ∀ i, (Q i).det ≠ 0) (p : ℕ) (S : HermForm K r)
    (hform : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    (x : Fin r → K) (h : ∀ v, Algebra.trace ℚ K (S.h v x) = 0) : x = 0 := by
  classical
  unfold jForm embVec at hform
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsingle : ∀ (j : Fin r) (b : K),
      (fun a => σ i₀ ((Pi.single j b : Fin r → K) a)) = (Pi.single j (σ i₀ b) : Fin r → ℂ) := by
    intro j b
    funext a
    by_cases ha : a = j
    · subst ha
      simp
    · simp [Pi.single_eq_of_ne ha]
  have hcol : ∀ (j : Fin r) (z : ℂ) (k : Fin r), (Q i₀ *ᵥ (Pi.single j z : Fin r → ℂ)) k = Q i₀ k j * z := by
    intro j z k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hg : ∀ j : Fin r, S.h (Pi.single j 1) x = 0 := by
    intro j
    have hlin : ∀ b : K, S.h (Pi.single j b) x = S.1 b * S.h (Pi.single j 1) x := by
      intro b
      apply (σ i₀).injective
      rw [map_mul, hform, hform, hsingle, hsingle, S.3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcol, hcol, map_one]
      simp only [map_mul, map_one]
      ring
    by_contra hg0
    have ht := h (Pi.single j (S.1 (S.h (Pi.single j 1) x)⁻¹))
    have ht2 := hlin (S.1 (S.h (Pi.single j 1) x)⁻¹)
    rw [ht2, S.2, inv_mul_cancel₀ hg0] at ht
    exact trace_one_ne ht
  have hw : (Q i₀)ᴴ *ᵥ (fun k => sgn p k * (Q i₀ *ᵥ fun a => σ i₀ (x a)) k) = 0 := by
    funext j
    have h0 := congrArg (σ i₀) (hg j)
    rw [hform, hsingle, map_zero] at h0
    show ∑ k, (Q i₀)ᴴ j k * (sgn p k * (Q i₀ *ᵥ fun a => σ i₀ (x a)) k) = 0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol, map_one, mul_one, Matrix.conjTranspose_apply, starRingEnd_apply]
    ring
  have hdet : ((Q i₀)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr (hQ i₀)
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  have hu0 : (Q i₀ *ᵥ fun a => σ i₀ (x a)) = 0 := by
    funext k
    have hk := congrFun hw0 k
    simp only [Pi.zero_apply] at hk ⊢
    rcases mul_eq_zero.mp hk with hk | hk
    · unfold sgn at hk
      split_ifs at hk <;> norm_num at hk
    · exact hk
  have hx0 := Matrix.eq_zero_of_mulVec_eq_zero (hQ i₀) hu0
  funext a
  have ha := congrFun hx0 a
  simp only [Pi.zero_apply] at ha ⊢
  exact (σ i₀).injective (by rw [ha, map_zero])

end Formalism.L2.Pj.FundamentalDomainD5
