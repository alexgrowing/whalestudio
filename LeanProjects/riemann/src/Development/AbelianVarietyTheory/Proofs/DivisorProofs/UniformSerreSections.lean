import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfCompatibleFractionsStatement
open MvPolynomial

namespace GlobalTheory.UniformSerre

variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}

noncomputable def comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) : MvPolynomial σ R :=
  ∑ m ∈ Q.support, monomial m ((coeff m Q).val.coeff e)

theorem coeff_comp (e : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (comp e Q) = (coeff m Q).val.coeff e := by
  classical
  rw [comp, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; rw [h]; simp

open scoped Classical in

noncomputable def liftFun (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, (mem_reesAlgebra_iff I _).2 (fun i => by
    rw [Polynomial.coeff_monomial]; split_ifs with hi
    · subst hi; exact h
    · exact zero_mem _)⟩ else 0

theorem liftFun_zero (e : ℕ) : liftFun I e 0 = 0 := by
  unfold liftFun; rw [dif_pos (zero_mem _)]; ext1; simp

noncomputable def lift (I : Ideal R) (e : ℕ) (P : MvPolynomial σ R) : MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ P.support, monomial m (liftFun I e (coeff m P))

theorem coeff_lift (e : ℕ) (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (lift I e P) = liftFun I e (coeff m P) := by
  classical
  rw [lift, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; rw [h, liftFun_zero]

theorem comp_lift (e e' : ℕ) (P : MvPolynomial σ R) (hP : ∀ m, coeff m P ∈ I ^ e) :
    comp e' (lift I e P) = if e' = e then P else 0 := by
  ext m
  rw [coeff_comp, coeff_lift]
  unfold liftFun; rw [dif_pos (hP m)]
  show (Polynomial.monomial e (coeff m P)).coeff e' = _
  rw [Polynomial.coeff_monomial]
  by_cases h : e' = e
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (Ne.symm h), if_neg h, coeff_zero]

theorem comp_sub (e : ℕ) (Q₁ Q₂ : MvPolynomial σ (reesAlgebra I)) :
    comp e (Q₁ - Q₂) = comp e Q₁ - comp e Q₂ := by
  ext m; rw [coeff_sub, coeff_comp, coeff_comp, coeff_comp, coeff_sub]
  exact Polynomial.coeff_sub _ _ _

theorem comp_X_pow_mul (e : ℕ) (k : σ) (L : ℕ) (Q : MvPolynomial σ (reesAlgebra I)) :
    comp e (X k ^ L * Q) = X k ^ L * comp e Q := by
  ext m
  rw [coeff_comp, X_pow_eq_monomial, X_pow_eq_monomial, coeff_monomial_mul', coeff_monomial_mul']
  split_ifs <;> simp [coeff_comp]

theorem isHomogeneous_lift {e t : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous t) :
    (lift I e P).IsHomogeneous t :=
  fun d hd => hP (fun h0 => hd (by rw [coeff_lift, h0, liftFun_zero]))

theorem isHomogeneous_comp {e t : ℕ} {Q : MvPolynomial σ (reesAlgebra I)} (hQ : Q.IsHomogeneous t) :
    (comp e Q).IsHomogeneous t :=
  fun d hd => hQ (fun h0 => hd (by rw [coeff_comp, h0]; simp))

theorem isHomogeneous_sub' {S : Type} [CommRing S] {P Q : MvPolynomial σ S} {t : ℕ}
    (hP : P.IsHomogeneous t) (hQ : Q.IsHomogeneous t) : (P - Q).IsHomogeneous t := by
  rw [← mem_homogeneousSubmodule] at *; exact Submodule.sub_mem _ hP hQ

end GlobalTheory.UniformSerre

open GlobalTheory.UniformSerre in

theorem GlobalTheory.uniform_serre_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i m, coeff m (F i) ∈ I ^ e) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous d ∧ (∀ m, coeff m G ∈ I ^ e) ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ L * (F i - X i ^ N * G) ∈ J e := by
  intro R _ _ I n J hJ
  obtain ⟨𝔞, hgr, hmem⟩ := GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra R I n J hJ
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.exists_homogeneous_form_of_compatible_fractions (reesAlgebra I) n 𝔞 hgr
  refine ⟨d₀, fun d hd e N F hFh hFc hFcomp => ?_⟩
  have hmemiff : ∀ t (H : MvPolynomial (Fin (n+1)) (reesAlgebra I)), H.IsHomogeneous t →
      (H ∈ 𝔞 ↔ ∀ e', comp e' H ∈ J e') := by
    intro t H hH
    rw [hmem t H hH]
    constructor
    · intro h e'; exact h e' _ (fun m => coeff_comp e' H m)
    · intro h e' G hG
      have : G = comp e' H := by ext m; rw [hG m, coeff_comp]
      rw [this]; exact h e'
  obtain ⟨G', hG'h, hG'⟩ := hd₀ d hd N (fun i => lift I e (F i)) (fun i => isHomogeneous_lift (hFh i)) (by
    intro i j
    obtain ⟨L, hL⟩ := hFcomp i j
    refine ⟨L, ?_⟩
    have hhom := ((((isHomogeneous_X (reesAlgebra I) i).mul (isHomogeneous_X _ j)).pow L).mul
      (isHomogeneous_sub' (((isHomogeneous_X _ j).pow N).mul (isHomogeneous_lift (I := I) (e := e) (hFh i)))
        (((isHomogeneous_X _ i).pow N).mul (isHomogeneous_lift (I := I) (e := e) (hFh j)))))
    rw [hmemiff _ _ hhom]
    intro e'
    rw [mul_pow, mul_assoc, comp_X_pow_mul, comp_X_pow_mul, comp_sub, comp_X_pow_mul, comp_X_pow_mul,
      comp_lift _ _ _ (hFc i), comp_lift _ _ _ (hFc j)]
    split_ifs with h
    · subst h; rw [← mul_assoc, ← mul_pow]; exact hL
    · simp)
  refine ⟨comp e G', isHomogeneous_comp hG'h, fun m => ?_, fun i => ?_⟩
  · rw [coeff_comp]; exact (mem_reesAlgebra_iff I _).1 (coeff m G').2 e
  · obtain ⟨L, hL⟩ := hG' i
    refine ⟨L, ?_⟩
    have hhom := ((isHomogeneous_X (reesAlgebra I) i).pow L).mul
      (isHomogeneous_sub' (isHomogeneous_lift (I := I) (e := e) (hFh i))
        (by rw [show d + N = 1 * N + d by ring]; exact ((isHomogeneous_X _ i).pow N).mul hG'h))
    have := (hmemiff _ _ hhom).1 hL e
    rwa [comp_X_pow_mul, comp_sub, comp_X_pow_mul, comp_lift _ _ _ (hFc i), if_pos rfl] at this
