import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreSectionsStatement
open MvPolynomial

namespace GlobalTheory.UnifCorr

variable {R : Type} [CommRing R] {σ : Type}

theorem coeff_X_pow_mul_mem (I : Ideal R) (i : σ) (k : ℕ) (G : MvPolynomial σ R)
    (h : ∀ m, coeff m G ∈ I) : ∀ m, coeff m ((X i : MvPolynomial σ R) ^ k * G) ∈ I := by
  intro m
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs
  · exact I.mul_mem_left _ (h _)
  · exact I.zero_mem

theorem mem_of_coeff_mem (I : Ideal R) (K : Ideal (MvPolynomial σ R))
    (hC : ∀ a ∈ I, C a ∈ K) (G : MvPolynomial σ R) (h : ∀ m, coeff m G ∈ I) : G ∈ K := by
  rw [G.as_sum]
  refine K.sum_mem fun v _ => ?_
  rw [← mul_one (coeff v G), ← C_mul_monomial]
  exact K.mul_mem_right _ (hC _ (h v))

end GlobalTheory.UnifCorr

open GlobalTheory.UnifCorr in
theorem GlobalTheory.homogeneous_correction_next_level : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ i, ∃ N : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F ∈ K e) → F ∈ K e) → (∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e) → (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, coeff m G ∈ I ^ (e + 1)) ∧ (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F - G ∈ K (e + 1)) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ m, coeff m G ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1) := by
  intro R _ _ I n K hsat hC hstep
  have hcoef : ∀ e (G : MvPolynomial (Fin (n + 1)) R), (∀ m, coeff m G ∈ I ^ (e + 1)) → G ∈ K e :=
    fun e G h => mem_of_coeff_mem (I ^ (e + 1)) (K e) (hC e) G h
  have hJ : ∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t →
      (∀ m, coeff m F ∈ I ^ e) → F ∈ K e → C a * F ∈ K (e + 1) := by
    intro e t a F ha hF _ hFK
    have hCF : (C a * F).IsHomogeneous t := by
      have := (isHomogeneous_C (Fin (n + 1)) a).mul hF
      rwa [zero_add] at this
    apply hsat (e + 1) t (C a * F) hCF
    intro i
    obtain ⟨N, G, _, hGc, hk⟩ := hstep e t F hF hFK i
    refine ⟨N, ?_⟩
    have h1 : C a * G ∈ K (e + 1) := by
      apply hcoef (e + 1)
      intro m
      rw [coeff_C_mul]
      have := Ideal.mul_mem_mul ha (hGc m)
      rwa [← pow_succ'] at this
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ N * (C a * F) = C a * (X i ^ N * F - G) + C a * G := by ring
    rw [this]
    exact add_mem ((K (e + 1)).mul_mem_left _ hk) h1
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_sections_alt R I n K hJ
  refine ⟨d₀, fun t ht e F hF hFK => ?_⟩
  choose N G hG hGc hk using hstep e t F hF hFK
  obtain ⟨M, hNM⟩ : ∃ M, ∀ i, N i ≤ M :=
    ⟨∑ i, N i, fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)⟩
  let G' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := fun i => X i ^ (M - N i) * G i
  have hXM : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M = X i ^ (M - N i) * X i ^ N i := fun i => by
    rw [← pow_add, Nat.sub_add_cancel (hNM i)]
  have hG'h : ∀ i, (G' i).IsHomogeneous (t + M) := fun i => by
    show (X i ^ (M - N i) * G i).IsHomogeneous (t + M)
    rw [show t + M = (M - N i) + (t + N i) by have := hNM i; omega]
    exact (isHomogeneous_X_pow i (M - N i)).mul (hG i)
  have hG'c : ∀ i m, coeff m (G' i) ∈ I ^ (e + 1) := fun i => coeff_X_pow_mul_mem _ i _ _ (hGc i)
  have hk' : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i ∈ K (e + 1) := fun i => by
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i = X i ^ (M - N i) * (X i ^ N i * F - G i) := by
      simp only [G', hXM i]; ring
    rw [this]; exact (K (e + 1)).mul_mem_left _ (hk i)
  obtain ⟨G0, hG0, hG0c, hL⟩ := hd₀ t ht (e + 1) M G' hG'h hG'c (fun i j => ⟨0, by
    have : ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ 0 * (X j ^ M * G' i - X i ^ M * G' j)
        = X i ^ M * (X j ^ M * F - G' j) - X j ^ M * (X i ^ M * F - G' i) := by ring
    rw [this]
    exact sub_mem ((K (e + 1)).mul_mem_left _ (hk' j)) ((K (e + 1)).mul_mem_left _ (hk' i))⟩)
  refine ⟨G0, hG0, hG0c, ?_⟩
  apply hsat (e + 1) t (F - G0) (hF.sub hG0)
  intro i
  obtain ⟨L, hLi⟩ := hL i
  refine ⟨L + M, ?_⟩
  have : (X i : MvPolynomial (Fin (n + 1)) R) ^ (L + M) * (F - G0)
      = X i ^ L * (X i ^ M * F - G' i) + X i ^ L * (G' i - X i ^ M * G0) := by ring
  rw [this]
  exact add_mem ((K (e + 1)).mul_mem_left _ (hk' i)) hLi
