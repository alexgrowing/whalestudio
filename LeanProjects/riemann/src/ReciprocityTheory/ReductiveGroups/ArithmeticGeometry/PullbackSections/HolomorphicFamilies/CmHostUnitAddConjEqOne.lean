import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate WithZero

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem imaginary_root_conj : conj H.rt0 = -H.rt0 := by
  rcases H with ⟨d, -, hp, -, -, -, -, -, -, -, r, hr⟩
  show conj r = -r
  have hdpos : (0:ℝ) < d := by exact_mod_cast hp.pos
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hre : r.re = 0 := by
    rcases mul_eq_zero.mp (show r.re * r.im = 0 by linarith) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      nlinarith [sq_nonneg r.re]
  apply Complex.ext <;> simp [hre]

theorem imaginary_root_ne_zero : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h, zero_pow two_ne_zero, zero_eq_neg] at h2
  exact H.d_prime.ne_zero (by exact_mod_cast h2)

theorem emb_rt (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have h : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]
    simp
  have h' : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
    have e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = τ (H.rt : E) ^ 2 - H.rt0 ^ 2 := by ring
    rw [e, h, sub_self]
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

theorem inPsi_or (τ : E →+* ℂ) : InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases emb_rt H τ with h | h
  · exact Or.inl h
  · right
    rw [h, map_neg, imaginary_root_conj, neg_neg]

theorem not_inPsi_both (τ : E →+* ℂ) : ¬ (InPsi H τ ∧ InPsi H (ComplexEmbedding.conjugate τ)) := by
  rintro ⟨h1, h2⟩
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1, imaginary_root_conj] at h2
  have h3 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact two_ne_zero h4
  · exact imaginary_root_ne_zero H h4

theorem bar_rt : H.bar H.rt = -H.rt := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  have key : τ ((H.bar H.rt : 𝓞 E) : E) = τ (-((H.rt : 𝓞 E) : E)) := by
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, map_neg]
    rcases emb_rt H τ with h | h <;> rw [h] <;> simp [imaginary_root_conj]
  have := τ.injective key
  rw [this]
  simp

theorem cmHostUnit_add_conj_eq_one : H.w0 + H.bar H.w0 = 1 := by
  have hb := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, bar_rt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

end Host

section RQ

end RQ

section Letters

open MvPolynomial

variable {T : Type} {r : T → ℕ} {n : ℕ}

def lEq : Letter T r n ≃ (Σ σ : T, Fin (r σ)) × Fin n where
  toFun x := (⟨x.1, x.2.1⟩, x.2.2)
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_rename {k : Type} [CommRing k] (P : MvPolynomial (Letter T r n) k)
    (G : ((Σ σ : T, Fin (r σ)) × Fin n →₀ ℕ) → k) :
    ∑ mo ∈ (rename (lEq (T := T) (r := r) (n := n)) P).support, (rename lEq P).coeff mo * G mo =
      ∑ mo ∈ P.support, P.coeff mo * G (Finsupp.mapDomain lEq mo) := by
  classical
  rw [support_rename_of_injective lEq.injective, Finset.sum_image]
  · refine Finset.sum_congr rfl fun mo _ => ?_
    rw [coeff_rename_mapDomain lEq lEq.injective]
  · intro x _ y _ h
    exact Finsupp.mapDomain_injective lEq.injective h

theorem coeff_rename_mem {k : Type} [CommRing k] (S : Subring k) (P : MvPolynomial (Letter T r n) k)
    (hP : ∀ m, P.coeff m ∈ S) (mo : (Σ σ : T, Fin (r σ)) × Fin n →₀ ℕ) :
    (rename (lEq (T := T) (r := r) (n := n)) P).coeff mo ∈ S := by
  classical
  by_cases h : mo ∈ (rename (lEq (T := T) (r := r) (n := n)) P).support
  · rw [support_rename_of_injective lEq.injective, Finset.mem_image] at h
    obtain ⟨m0, _, rfl⟩ := h
    rw [coeff_rename_mapDomain lEq lEq.injective]
    exact hP m0
  · rw [notMem_support_iff.1 h]
    exact S.zero_mem

theorem harm_rename [Fintype T] {k : Type} [Field k] (cc : T → T) (isX : T → Prop)
    (P : MvPolynomial (Letter T r n) k) (hP : P ∈ harmK r n k cc isX (fun _ => 1)) (τ : T) (hτ : isX τ)
    (i : Fin (r τ)) (i' : Fin (r (cc τ))) :
    ∑ b : Fin n, pderiv (((⟨τ, i⟩ : Σ σ : T, Fin (r σ))), b)
      (pderiv (((⟨cc τ, i'⟩ : Σ σ : T, Fin (r σ))), b) (rename (lEq (T := T) (r := r) (n := n)) P)) = 0 := by
  classical
  have h := hP
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h
  have h2 := h τ hτ i i'
  simp only [lap, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at h2
  have h3 : ∑ x : Fin n, pderiv (⟨τ, i, x⟩ : Letter T r n) (pderiv (⟨cc τ, i', x⟩ : Letter T r n) P) = 0 := by
    simpa [LinearMap.sum_apply] using h2
  have e : ∀ b : Fin n, pderiv (((⟨τ, i⟩ : Σ σ : T, Fin (r σ))), b)
      (pderiv (((⟨cc τ, i'⟩ : Σ σ : T, Fin (r σ))), b) (rename (lEq (T := T) (r := r) (n := n)) P)) =
      rename lEq (pderiv (⟨τ, i, b⟩ : Letter T r n) (pderiv (⟨cc τ, i', b⟩ : Letter T r n) P)) := by
    intro b
    show pderiv (lEq ⟨τ, i, b⟩) (pderiv (lEq ⟨cc τ, i', b⟩) (rename lEq P)) = _
    rw [pderiv_rename lEq.injective, pderiv_rename lEq.injective]
  simp only [e, ← map_sum, h3, map_zero]

end Letters

end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
